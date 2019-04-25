//! Types and methods for a simple, free-space bitmap data structure.
//!
//! # Examples
//! ```
//! use bitmap::{BitMap, BitStatus};
//!
//! let mut buffer = [0b01110000];
//! let bmap = unsafe { BitMap::from_raw_parts(buffer.as_mut_ptr(), buffer.len()) };
//!
//! bmap.put(0, BitStatus::Set);
//! assert_eq!(bmap.get(0).unwrap(), BitStatus::Set);
//! assert_eq!(bmap[0], 0b11110000);
//! ```

use core::marker::PhantomData;
use core::ops::Index;
use core::ops::IndexMut;

/// `BitStatus` represents the the value of a bit in a `BitMap`.
///
/// Unset corresponds to a value of 0.
/// Set corresponds to a value of 1.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
#[repr(u8)]
pub enum BitStatus {
    Unset = 0,
    Set = 1,
}

/// A bitmap.
pub struct BitMap<'a> {
    start: *mut u8,
    byte_length: usize,
    phantom: PhantomData<&'a u8>,
}

impl<'a> BitMap<'a> {
    /// Create a new `BitMap` with the given raw pointer and byte-length.
    pub unsafe fn from_raw_parts(start: *mut u8, byte_length: usize) -> BitMap<'a> {
        BitMap {
            start,
            byte_length,
            phantom: PhantomData,
        }
    }

    /// Returns a `Option<&mut u8>` referencing the byte at the given byte-index.
    ///
    /// Returns `None` if the index is out of bounds.
    pub fn byte_at(&self, byte_idx: usize) -> Option<&mut u8> {
        if byte_idx >= self.byte_length {
            None
        } else {
            unsafe { self.start.add(byte_idx).as_mut() }
        }
    }

    /// Returns a `Option<BitStatus>` for the bit at the given bit-index.
    ///
    /// Returns `None` if the index is out of bounds.
    pub fn get(&self, idx: usize) -> Option<BitStatus> {
        let target_byte = idx >> 3;
        let offset = idx % 8;
        self.byte_at(target_byte)
            .map(|b| (*b >> (7 - offset)) & 0x1)
            .map(|bit| {
                if bit == 0 {
                    BitStatus::Unset
                } else {
                    BitStatus::Set
                }
            })
    }

    /// Stores the given `BitStatus` for the bit at the given bit-index.
    ///
    /// Returns `Some(())` on success and `None` if the index is out of bounds.
    pub fn put(&self, idx: usize, status: BitStatus) -> Option<()> {
        let target_byte = idx >> 3;
        let offset = idx % 8;
        self.byte_at(target_byte).map(|byte| {
            let mask = 0x1 << (7 - offset);
            match status {
                BitStatus::Set => *byte |= mask,
                BitStatus::Unset => *byte ^= mask,
            };
        })
    }
}

impl<'a> Index<usize> for BitMap<'a> {
    type Output = u8;

    fn index(&self, index: usize) -> &u8 {
        self.byte_at(index).unwrap()
    }
}

impl<'a> IndexMut<usize> for BitMap<'a> {
    fn index_mut(&mut self, index: usize) -> &mut u8 {
        self.byte_at(index).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn byte_at_0() {
        let mut buffer = [0b00001111];
        let bmap = unsafe { BitMap::from_raw_parts(buffer.as_mut_ptr(), buffer.len()) };
        assert_eq!(bmap.byte_at(0).unwrap(), &0b00001111);
    }

    #[test]
    fn byte_at_1() {
        let mut buffer = [0b00000000, 0b00000000];
        let bmap = unsafe { BitMap::from_raw_parts(buffer.as_mut_ptr(), buffer.len()) };
        let byte = bmap.byte_at(1).unwrap();
        *byte = 0b00001111;
        assert_eq!(bmap.byte_at(0).unwrap(), &0b00000000);
        assert_eq!(bmap.byte_at(1).unwrap(), &0b00001111);
    }

    #[test]
    fn index() {
        let mut buffer = [0b00001111];
        let bmap = unsafe { BitMap::from_raw_parts(buffer.as_mut_ptr(), buffer.len()) };
        assert_eq!(bmap[0], 0b00001111);
    }

    #[test]
    fn index_mut() {
        let mut buffer = [0b00000000];
        let mut bmap = unsafe { BitMap::from_raw_parts(buffer.as_mut_ptr(), buffer.len()) };
        bmap[0] |= 0b00001111;
        assert_eq!(bmap[0], 0b00001111);
    }

    #[test]
    fn get_byte_0() {
        let mut buffer = [0b00001111];
        let bmap = unsafe { BitMap::from_raw_parts(buffer.as_mut_ptr(), buffer.len()) };
        for i in 0..4 {
            assert_eq!(bmap.get(i).unwrap(), BitStatus::Unset);
        }
        for i in 4..8 {
            assert_eq!(bmap.get(i).unwrap(), BitStatus::Set);
        }
    }

    #[test]
    fn get_byte_1() {
        let mut buffer = [0b00000000, 0b00001111];
        let bmap = unsafe { BitMap::from_raw_parts(buffer.as_mut_ptr(), buffer.len()) };
        for i in 8..12 {
            assert_eq!(bmap.get(i).unwrap(), BitStatus::Unset);
        }
        for i in 12..16 {
            assert_eq!(bmap.get(i).unwrap(), BitStatus::Set);
        }
    }

    #[test]
    fn get_index_out_of_bounds() {
        let mut buffer = [0b00001111];
        let bmap = unsafe { BitMap::from_raw_parts(buffer.as_mut_ptr(), buffer.len()) };
        assert_eq!(bmap.get(8), None);
        assert_eq!(bmap.get(!0), None);
    }

    #[test]
    fn put_byte_0() {
        let mut buffer = [0b01110000];
        let bmap = unsafe { BitMap::from_raw_parts(buffer.as_mut_ptr(), buffer.len()) };
        bmap.put(0, BitStatus::Set);
        for i in 0..4 {
            assert_eq!(bmap.get(i).unwrap(), BitStatus::Set);
        }
        for i in 4..8 {
            assert_eq!(bmap.get(i).unwrap(), BitStatus::Unset);
        }
    }

    #[test]
    fn put_byte_1() {
        let mut buffer = [0b01110000];
        let bmap = unsafe { BitMap::from_raw_parts(buffer.as_mut_ptr(), buffer.len()) };
        bmap.put(0, BitStatus::Set);
        for i in 0..4 {
            assert_eq!(bmap.get(i).unwrap(), BitStatus::Set);
        }
        for i in 4..8 {
            assert_eq!(bmap.get(i).unwrap(), BitStatus::Unset);
        }
    }

    #[test]
    fn put_index_out_of_bounds() {
        let mut buffer = [0b00001111];
        let bmap = unsafe { BitMap::from_raw_parts(buffer.as_mut_ptr(), buffer.len()) };
        assert_eq!(bmap.put(8, BitStatus::Set), None);
        assert_eq!(bmap.put(!0, BitStatus::Set), None);
    }
}