//
// # Exercise Expectations
//
// The goal here to is to establish a basis for our technical interview,
// and be able to discuss the choices you made and why. We're far more interested
// in the discussion part than receiving a perfect implementation of the following
// exercise. The exercise is not designed to take too long of your personal time,
// and doesn't have to be completed fully (although, bonus point if it is). We estimate
// it should be achieveable to complete between 1 to 2 hours of dedicated time.
//
// We don't expect rust expertise, but you *need* to have at least the basic fluency
// with the rust syntax, and we expect that the following module compiles.
//
// Please keep this exercise private, and don't make your result available publically.
//
// # Recap about Blockchain:
//
// A blockchain is organised as sequence of blocks.
//
//      Block 0 (Genesis) <- Block 1 <- Block 2 <- ...
//
// Block i is a parent of Block i+1
// Block i+1 is a child of Block i
//
// Each block has a specific hash, that are considered unique, and each blocks contains a reference to
// its parent block's hash.
//
// The first block is called genesis, and doesn't have a parent; this is the oldest block in the chain.
// The latest block is often called the tip of the chain and is the yougest block added to the chain.
//
// The blockchain has a process that allows different entities to add blocks to the chain,
// to create a "distributed database". Each distributed entities maintains one version of the tip,
// that combines make a tree of blocks, where the common part are the previously agreed block history
//
// # Let's get started:
//
// The goal of this module is to define a in-memory blockchain in rust where we
// enforce the usual invariants that make a valid blockchain. we omitted any
// blockchain contents, and stripped the block to the minimal: its parent block
// hash, and a monotonically increasing numbers serving as timestamp.
//
// The invariant we have are standard: * the parent hash of a block. should
// match the hash of the parent * all children blocks of a given block should
//
// We define the basis of our exercise with the following definitions:
// ********************************************************************************

static mut FOO: u32 = 0;

/// Block Hash
type BlockHash = u64;

/// Block number (monotonically increasing)
type BlockNumber = u32;

#[derive(Clone, Debug)]
pub struct BlockChain {
    block: Block,
    parent: Option<Box<BlockChain>>,
}

impl BlockChain {
    fn new(count: u32) -> BlockChain {
        let mut chain = BlockChain {
            block: Block::new(0, 0),
            parent: None
        };

        for id in 1..count {
            chain = BlockChain {
                block: Block::new(id, hash_of_block(&chain.block)),
                parent: Some(Box::new(chain))
            };
        }

        chain
    }

    fn fork(&self, count: usize) -> Vec<BlockChain> {
        let mut fork_chain: Vec<BlockChain> = Vec::with_capacity(count);

        let hash = hash_of_block(&self.block);
        let id = self.block.number + 1;

        for _ in 0..count {
            fork_chain.push(
                BlockChain {
                    block: Block::new(id, hash),
                    parent: Some(Box::new(self.clone()))
                }
            );
        }

        fork_chain
    }

    fn extend(self) -> BlockChain {
        let new_block = Block::new(self.block.number + 1,
                                             hash_of_block(&self.block));

        BlockChain{block: new_block, parent: Some(Box::new(self))}
    }
}

use std::fmt;
impl fmt::Display for BlockChain {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {

        write!(f, "{}\n", "----------------------------- Chain: ---------------------------------");

        for block in self {
            write!(f, "{:?}\n", block);
        }

        write!(f, "{}\n", "----------------------------------------------------------------------");

        Ok(())
    }
}

impl<'a> IntoIterator for &'a BlockChain {
    type Item = &'a Block;
    type IntoIter = IterBlockChain<'a>;

    fn into_iter(self) -> Self::IntoIter {
        IterBlockChain {chain: Some(self)}
    }
}

pub struct IterBlockChain<'a> {
    chain: Option<&'a BlockChain>,
}

impl<'a> Iterator for IterBlockChain<'a> {
    type Item = &'a Block;

    fn next(&mut self) -> Option<Self::Item> {

        let mut block: Option<Self::Item> = None;
        let mut next_parent: Option<&'a BlockChain> = None;

        if let Some(ref chain) = self.chain {

            block = Some(&chain.block);

            if let Some(ref parent) = chain.parent {
                next_parent = Some(&**parent);
            } else {
                next_parent = None;
            }
        }

        self.chain = next_parent;

        block
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct BlockContent {
    /* block contents omitted */
    foo: u32, // for simplifying
}

/// A typical block
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Block {
    number: BlockNumber,
    parent_hash: BlockHash,
    content: BlockContent,
}

impl Block {
    fn new(id: u32, parent_hash: BlockHash) -> Block {
        let block: Block;

        unsafe {
            block = Block{number: id, parent_hash, content: BlockContent{foo: FOO }};
            FOO += 1;
        }

        block
    }
}

/// calculate the BlockHash associated with a Block
pub fn hash_of_block(block: &Block) -> BlockHash {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut s = DefaultHasher::new();
    block.number.hash(&mut s);
    block.parent_hash.hash(&mut s);
    block.content.hash(&mut s); // add to make difference between blocks
    s.finish()
}

//********************************************************************************
// Part 1.1: define a function to append a block to the blockchain
// make sure that only valid blockchain are created
//********************************************************************************
fn block_append(blockchain: BlockChain, block: Block) -> Option<BlockChain> {

    let parent_hash = hash_of_block(&blockchain.block);
    let next_number = blockchain.block.number + 1;

    let mut chain = BlockChain{block, parent: Some(Box::new(blockchain))};

    chain.block.number = next_number;
    chain.block.parent_hash = parent_hash;

    Some(chain)
}

//********************************************************************************
// Part 1.2: Given a block hash, search in the blockchain for the block associated
//********************************************************************************
fn block_lookup(blockchain: &BlockChain, hash: BlockHash) -> Option<Block> {

    let mut other_hash = hash_of_block(&blockchain.block);

    for block in blockchain {
        if hash == other_hash {
            return Some(block.clone());
        }
        other_hash = block.parent_hash;
    }

    None
}

//********************************************************************************
// Part 1.3: Given a list of blockchains, returns the block that is the common ancestor if it exists
//
// The common ancestor is the youngest block in the blockchain that is common to
// each blockchains
//********************************************************************************
fn block_common_ancestor(blockchain: &[BlockChain]) -> Option<Block> {

    let count = blockchain.len();

    use std::collections::HashMap;

    let mut map: HashMap<BlockHash, (usize, &Block)> = HashMap::new();
    let mut hash: BlockHash;
    let mut iter: IterBlockChain;
    let mut block: &Block;

    // 1. count all bocks by their hashes
    for chain in blockchain {

        iter = chain.into_iter();
        block = iter.next().unwrap();
        hash = block.parent_hash;

        for block in iter {
            // data is tuple (count of hash, Block with that hash)
            if let Some(data) = map.get_mut(&hash) {

                // Blocks are differ by their content
//                if block == data.1 {
                    (*data).0 += 1;
//                }
                hash = block.parent_hash;

                continue;
            }

            map.insert(hash, (1, block));
            hash = block.parent_hash;
        }
    }

    // 2. find the earliest block with the greatest count
    let mut ancestor: Option<&Block> = None;
    let mut id: u32 = 0;

    for (_key, data) in map.iter() {
        if data.0 == count && data.1.number >= id {
            id = data.1.number;
            ancestor = Some(data.1);
        }
    }

    ancestor.map_or(None, |block| Some(block.clone()))
}

//********************************************************************************
// Part 1.4: Similar to part 1.2, but now we want to optimise the search to be as
// efficient as possible.
//
// Define an index structure that allow to optimise looking up by block hash and check
// for the existance of a block.
//
// Interesting point to consider is how to keep this index up-to-date and how it
// influences your choices of structure. Just like a blockchain that is updating,
// it would be beneficial to be able to create cheap fork of the index to represent
// fork of the blockchain.
// ********************************************************************************
use std::collections::HashMap;

#[derive(Debug)]
struct Index {
    hashes: HashMap<BlockHash, Block>,
    // but more efficient way is using the HashMap<BlockHash, &'a Block>
    // with lifetime parameter in the context of Index
}

impl Index {
    /// Given a blockchain, create the associated Index structure
    pub fn generate(blockchain: &BlockChain) -> Self {

        let mut hashes = HashMap::new();
        let mut hash = hash_of_block(&blockchain.block);

        for block in blockchain {
            hashes.insert(hash, block.clone());
            hash = block.parent_hash;
        }

        Index {hashes}
    }

    /// Lookup a block in the Blockchain, efficiently
    pub fn lookup(&self, hash: BlockHash) -> Option<Block> {
        self.hashes.get(&hash)
            .map_or(None, |block| Some(block.clone()) )
    }

    /// Check if a specific block hash in the blockchain exists
    pub fn exists(&self, hash: BlockHash) -> bool {
        self.hashes.contains_key(&hash)
    }
}

//********************************************************************************
// Part 2: Tests
//
// * Describe your process to tests some of the functions and properties.
// * Either in the form of valid rust code, or commented pseudo code.
//********************************************************************************
#[cfg(test)]
mod tests {
    use super::*;
    use std::vec::Vec;

    /// Common test about creation of blockchain
    #[test]
    fn test0() {
        let len = 4;
        let chain = BlockChain::new(len);

        assert_eq!(chain.into_iter().fold(0, |acc, _| acc + 1), len);
        assert_eq!(
            chain.into_iter().scan(len as i32, |prev, ref block| {
                let item = block.number as i32 - *prev;
                *prev = block.number as i32;
                Some(-item)
        }).sum::<i32>(), len as i32);
    }

    /// Test about append new block to chain
    #[test]
    fn test1() {
        let len = 2;
        let chain = BlockChain::new(len);

        assert_eq!(block_append(chain,
                                Block::new(0, 0))
            .map_or(None, |chain| Some(chain.block.number)), Some(len));
    }

    /// Test about looking up block by its hash (naive implementation)
    #[test]
    fn test2() {
        let len = 3;
        let chain = BlockChain::new(len);

        for block in &chain {
            assert_eq!(block_lookup(&chain, hash_of_block(block)), Some(block.clone()));
        }

        let out_block = Block::new(len + 1, 1); // this block isn't inside chain
        assert_eq!(block_lookup(&chain, hash_of_block(&out_block)), None);
    }

    /// Test about seeking common ancestor for a few versions of chains
    #[test]
    fn test3() {
        let len = 2;
        let chain = BlockChain::new(len);
        /* chain:
                  [block 0] <-- [block 1]
        */

        let mut chains = chain.fork(2)
            .iter().map(|chain| chain.clone().extend()).collect::<Vec<BlockChain>>();

        /* chains: [block 1] is common ancestor
                                             |<-- [block  2] <-- [block  3]
                  [block 0] <-- [block 1] <--|
                                             |<-- [block' 2] <-- [block' 3]
        */

        // test31: common ancestor is block with number 1 (second block in chain)
        let mut common: Option<Block> = block_common_ancestor(chains.as_slice());
        assert_eq!(common.unwrap().number, len-1);

        // =========================================================================================
        // test32: no common ancestor
        chains.push(BlockChain::new(2));
        /* chains:  no common ancestor
                                             |<-- [block  2] <-- [block  3]
                  [block 0] <-- [block 1] <--|
                                             |<-- [block' 2] <-- [block' 3]

                  [block' 0] <-- [block' 1]
        */

        common = block_common_ancestor(chains.as_slice());
        assert_eq!(common, None);
    }

    /// Test about checking existence of block inside chain
    #[test]
    fn test41() {
        let len = 3;
        let chain = BlockChain::new(len);
        let mut iter = chain.into_iter();

        let index = Index::generate(&chain);

        let tip = iter.next().unwrap();

        assert_eq!(index.exists(hash_of_block(&tip)), true);  // match to tip
        assert_eq!(index.exists(tip.parent_hash), true);
        assert_eq!(index.exists(iter.next().unwrap().parent_hash), true);
        assert_eq!(index.exists(iter.next().unwrap().parent_hash), false); // match to genesis block
    }

    /// Test about looking up block by hash inside chain with complexity ~O(1)
    #[test]
    fn test42() {
        let len = 3;
        let chain = BlockChain::new(len);
        let mut iter = chain.into_iter();
        let mut iter2 = chain.into_iter();

        let index = Index::generate(&chain);

        let tip = iter.next().unwrap();

        assert_eq!(index.lookup(hash_of_block(&tip)).unwrap().content,
                   iter2.next().unwrap().content); // match to tip
        assert_eq!(index.lookup(tip.parent_hash).unwrap().content,
                   iter2.next().unwrap().content);
        assert_eq!(index.lookup(iter.next().unwrap().parent_hash).unwrap().content,
                   iter2.next().unwrap().content);
        assert_eq!(index.lookup(iter.next().unwrap().parent_hash),
                   None); // match to genesis block
    }
}