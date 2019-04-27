//! Types and methods for a simple, free-space bitmap data structure.
//!
//! NOTE: The `BitMap` type is designed to be low-level, i.e. it is created from a mutable raw
//! pointer and a length. It is meant, for example, to create a bitmap of free pages in DRAM for a
//! page allocator and NOT (as in the examples and test cases) to be created from an owned resource
//! such as an array, `Vec`, etc. as this violates Rust's rules about ownership and borrowing,
//! namely that a resource has a single owner (i.e. a binding) and that there is at most one
//! mutable reference to that resource at any given time. Please use this type with caution.
//!
//! # Examples
//! ```
//! use bitmap::{BitMap, BitStatus};
//!
//! let mut buffer = [0b01110000];
//! let mut bmap = unsafe { BitMap::from_raw_parts(buffer.as_mut_ptr(), buffer.len()) };
//!
//! bmap.put(0, BitStatus::Set);
//! assert_eq!(bmap.get(0).unwrap(), BitStatus::Set);
//! assert_eq!(bmap[0], 0b11110000);
//! ```
//!
//! ```
//! use bitmap::{BitMap, BitStatus};
//!
//! let mut buffer = [0b11111111, 0b11111111];
//! let mut bmap = unsafe { BitMap::from_raw_parts(buffer.as_mut_ptr(), buffer.len()) };
//!
//! bmap.put_range(5..16, BitStatus::Unset);
//! assert_eq!(bmap[0], 0b11111000);
//! assert_eq!(bmap[1], 0b00000000);
//! ```

use core::fmt;
use core::marker::PhantomData;
use core::ops::Index;
use core::ops::IndexMut;
use core::ops::Range;

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

impl<'a> fmt::Debug for BitMap<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut result = Ok(());
        for i in 0..(self.byte_length - 1) {
            result = write!(f, "{:08b} ", self[i]);
            if result.is_err() {
                return result;
            }
        }
        if self.byte_length > 0 {
            result = write!(f, "{:08b}", self[self.byte_length - 1]);
        }
        result
    }
}

impl<'a> BitMap<'a> {
    /// Create a new `BitMap` with the given raw pointer and length (in bytes).
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
    /// # Panics
    ///
    /// Panics if `idx` > 8 * `byte_length`.
    pub fn put(&mut self, idx: usize, status: BitStatus) {
        let target_byte = idx >> 3;
        let offset = idx % 8;
        if let None = self.byte_at(target_byte).map(|byte| {
            let mask = 0x1 << (7 - offset);
            match status {
                BitStatus::Set => *byte |= mask,
                BitStatus::Unset => *byte ^= mask,
            };
        }) {
            panic!(
                "index out of bounds: {} (bit-length: {})",
                idx,
                8 * self.byte_length
            );
        }
    }

    /// Stores the given `BitStatus` for the bits in the given range of bit-indices.
    ///
    /// # Panics
    ///
    /// Panics if `range.end` > 8 * `byte_length`.
    pub fn put_range(&mut self, range: Range<usize>, status: BitStatus) {
        if range.start >= range.end {
            return;
        }

        let start_byte = range.start >> 3;
        let end_byte = (range.end - 1) >> 3;

        if start_byte == end_byte {
            let left_mask = !0u8 >> (range.start % 8);
            let right_mask = !0u8 << (7 - ((range.end - 1) % 8));
            let mask = left_mask & right_mask;
            self[start_byte] |= mask;
        } else {
            let start_mask = !0u8 >> (range.start % 8);
            let end_mask = !0u8 << (7 - ((range.end - 1) % 8));

            if end_byte >= self.byte_length {
                panic!(
                    "range out of bounds: {:?} (bit-length: {})",
                    range,
                    8 * self.byte_length
                );
            }

            match status {
                BitStatus::Set => {
                    self[start_byte] |= start_mask;
                    self[end_byte] |= end_mask;
                    for i in (start_byte + 1)..end_byte {
                        self[i] |= !0u8;
                    }
                }
                BitStatus::Unset => {
                    self[start_byte] ^= start_mask;
                    self[end_byte] ^= end_mask;
                    for i in (start_byte + 1)..end_byte {
                        self[i] ^= !0u8;
                    }
                }
            }
        }
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
    fn fmt_1_byte() {
        let mut buffer = [0b00001111];
        let bmap = unsafe { BitMap::from_raw_parts(buffer.as_mut_ptr(), buffer.len()) };
        assert_eq!(format!("{:?}", bmap), "00001111");
    }

    #[test]
    fn fmt_2_bytes() {
        let mut buffer = [0b00001111, 0b10101010];
        let bmap = unsafe { BitMap::from_raw_parts(buffer.as_mut_ptr(), buffer.len()) };
        assert_eq!(format!("{:?}", bmap), "00001111 10101010");
    }

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
        let mut bmap = unsafe { BitMap::from_raw_parts(buffer.as_mut_ptr(), buffer.len()) };
        bmap.put(0, BitStatus::Set);
        assert_eq!(bmap[0], 0b11110000);
    }

    #[test]
    fn put_byte_1() {
        let mut buffer = [0b00000000, 0b01110000];
        let mut bmap = unsafe { BitMap::from_raw_parts(buffer.as_mut_ptr(), buffer.len()) };
        bmap.put(8, BitStatus::Set);
        assert_eq!(bmap[0], 0b00000000);
        assert_eq!(bmap[1], 0b11110000);
    }

    #[test]
    #[should_panic]
    fn put_index_out_of_bounds() {
        let mut buffer = [0b00001111];
        let mut bmap = unsafe { BitMap::from_raw_parts(buffer.as_mut_ptr(), buffer.len()) };
        bmap.put(8, BitStatus::Set);
    }

    #[test]
    fn put_range_empty() {
        let mut buffer = [0b00001111];
        let mut bmap = unsafe { BitMap::from_raw_parts(buffer.as_mut_ptr(), buffer.len()) };
        bmap.put_range(0..0, BitStatus::Set);
        assert_eq!(bmap[0], 0b00001111);
        bmap.put_range(7..7, BitStatus::Set);
        assert_eq!(bmap[0], 0b00001111);
        bmap.put_range(8..8, BitStatus::Set);
        assert_eq!(bmap[0], 0b00001111);
    }

    #[test]
    #[should_panic]
    fn put_range_panic() {
        let mut buffer = [0b00000000];
        let mut bmap = unsafe { BitMap::from_raw_parts(buffer.as_mut_ptr(), buffer.len()) };
        bmap.put_range(1..9, BitStatus::Set);
    }

    #[test]
    fn put_range_length_1() {
        let mut buffer = [0b00001111];
        let mut bmap = unsafe { BitMap::from_raw_parts(buffer.as_mut_ptr(), buffer.len()) };
        bmap.put_range(0..1, BitStatus::Set);
        assert_eq!(bmap[0], 0b10001111);
    }

    #[test]
    fn put_range_length_2() {
        let mut buffer = [0b00001111];
        let mut bmap = unsafe { BitMap::from_raw_parts(buffer.as_mut_ptr(), buffer.len()) };
        bmap.put_range(0..2, BitStatus::Set);
        assert_eq!(bmap[0], 0b11001111);
    }

    #[test]
    fn put_range_length_9() {
        let mut buffer = [0b11111111, 0b11111111];
        let mut bmap = unsafe { BitMap::from_raw_parts(buffer.as_mut_ptr(), buffer.len()) };
        bmap.put_range(4..12, BitStatus::Unset);
        assert_eq!(bmap[0], 0b11110000);
        assert_eq!(bmap[1], 0b00001111);
    }

    #[test]
    fn put_range_length_3_bytes() {
        let mut buffer = [0b11111111, 0b11111111, 0b11111111];
        let mut bmap = unsafe { BitMap::from_raw_parts(buffer.as_mut_ptr(), buffer.len()) };
        bmap.put_range(7..24, BitStatus::Unset);
        assert_eq!(bmap[0], 0b11111110);
        assert_eq!(bmap[1], 0b00000000);
        assert_eq!(bmap[2], 0b00000000);
    }

    #[test]
    fn put_range_length_4_bytes() {
        let mut buffer = [0b11111111, 0b11111111, 0b11111111, 0b11111111];
        let mut bmap = unsafe { BitMap::from_raw_parts(buffer.as_mut_ptr(), buffer.len()) };
        bmap.put_range(0..31, BitStatus::Unset);
        assert_eq!(bmap[0], 0b00000000);
        assert_eq!(bmap[1], 0b00000000);
        assert_eq!(bmap[2], 0b00000000);
        assert_eq!(bmap[3], 0b00000001);
    }
}
