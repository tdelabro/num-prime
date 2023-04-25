//! Implementations and extensions for [PrimeBuffer], which represents a container of primes
//!
//! In `num-prime`, there is no global instance to store primes, the user has to generate
//! and store the primes themselves. The trait [PrimeBuffer] defines a unified interface
//! for a prime number container. Some methods that can take advantage of pre-generated
//! primes will be implemented in the [PrimeBufferExt] trait.
//!
//! We also provide [NaiveBuffer] as a simple implementation of [PrimeBuffer] without any
//! external dependencies. The performance of the [NaiveBuffer] will not be extremely optimized,
//! but it will be efficient enough for most applications.
//!

use crate::tables::{SMALL_PRIMES, SMALL_PRIMES_NEXT};
use crate::traits::PrimeBuffer;
use bitvec::{bitvec, prelude::Msb0};
use core::iter;
use num_integer::Roots;

#[cfg(not(feature = "std"))]
use num_traits::float::FloatCore;

use crate::stdlib::slice;
use crate::stdlib::vec;
use crate::stdlib::Vec;

/// NaiveBuffer implements a very simple Sieve of Eratosthenes
pub struct NaiveBuffer {
    list: Vec<u64>, // list of found prime numbers
    next: u64, // all primes smaller than this value has to be in the prime list, should be an odd number
}

impl NaiveBuffer {
    #[inline]
    pub fn new() -> Self {
        let list = SMALL_PRIMES.iter().map(|&p| p as u64).collect();
        NaiveBuffer {
            list,
            next: SMALL_PRIMES_NEXT,
        }
    }
}

impl<'a> PrimeBuffer<'a> for NaiveBuffer {
    type PrimeIter = slice::Iter<'a, u64>;

    fn contains(&self, num: u64) -> bool {
        self.list.binary_search(&num).is_ok()
    }

    fn clear(&mut self) {
        self.list.truncate(16);
        self.list.shrink_to_fit();
        self.next = 55; // 16-th prime is 53
    }

    fn iter(&'a self) -> Self::PrimeIter {
        self.list.iter()
    }

    fn bound(&self) -> u64 {
        *self.list.last().unwrap()
    }

    fn reserve(&mut self, limit: u64) {
        let sieve_limit = (limit | 1) + 2; // make sure sieving limit is odd and larger than limit
        let current = self.next; // prevent borrowing self
        debug_assert!(current % 2 == 1);
        if sieve_limit < current {
            return;
        }

        // create sieve and filter with existing primes
        let mut sieve = bitvec![usize, Msb0; 0; ((sieve_limit - current) / 2) as usize];
        for p in self.list.iter().skip(1) {
            // skip pre-filtered 2
            let start = if p * p < current {
                p * ((current / p) | 1) // start from an odd factor
            } else {
                p * p
            };
            for multi in (start..sieve_limit).step_by(2 * (*p as usize)) {
                if multi >= current {
                    sieve.set(((multi - current) / 2) as usize, true);
                }
            }
        }

        // sieve with new primes
        for p in (current..Roots::sqrt(&sieve_limit) + 1).step_by(2) {
            for multi in (p * p..sieve_limit).step_by(2 * (p as usize)) {
                if multi >= current {
                    sieve.set(((multi - current) / 2) as usize, true);
                }
            }
        }

        // collect the sieve
        self.list
            .extend(sieve.iter_zeros().map(|x| (x as u64) * 2 + current));
        self.next = sieve_limit;
    }
}

impl NaiveBuffer {
    // FIXME: These functions could be implemented in the trait, but only after
    // RFC 2071 and https://github.com/cramertj/impl-trait-goals/issues/3

    /// Returns all primes ≤ `limit`. The primes are sorted.
    // TODO: let primes return &[u64] instead of iterator, and create a separate iterator
    //       for endless prime iter. This can be a method in this trait, or standalone function,
    //       or implement as IntoIter. We can try to implement PrimeBuffer on primal first and see
    //       if it's reasonable to unifiy
    pub fn primes(&mut self, limit: u64) -> iter::Take<<Self as PrimeBuffer>::PrimeIter> {
        self.reserve(limit);
        let position = match self.list.binary_search(&limit) {
            Ok(p) => p + 1,
            Err(p) => p,
        }; // into_ok_or_err()
        return self.list.iter().take(position);
    }

    /// Returns all primes ≤ `limit` and takes ownership. The primes are sorted.
    pub fn into_primes(mut self, limit: u64) -> vec::IntoIter<u64> {
        self.reserve(limit);
        let position = match self.list.binary_search(&limit) {
            Ok(p) => p + 1,
            Err(p) => p,
        }; // into_ok_or_err()
        self.list.truncate(position);
        return self.list.into_iter();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prime_generation_test() {
        const PRIME50: [u64; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47];
        const PRIME300: [u64; 62] = [
            2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83,
            89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179,
            181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271,
            277, 281, 283, 293,
        ];

        let mut pb = NaiveBuffer::new();
        assert_eq!(pb.primes(50).cloned().collect::<Vec<_>>(), PRIME50);
        assert_eq!(pb.primes(300).cloned().collect::<Vec<_>>(), PRIME300);

        // test when limit itself is a prime
        pb.clear();
        assert_eq!(pb.primes(293).cloned().collect::<Vec<_>>(), PRIME300);
        pb = NaiveBuffer::new();
        assert_eq!(*pb.primes(257).last().unwrap(), 257); // boundary of small table
        pb = NaiveBuffer::new();
        assert_eq!(*pb.primes(8167).last().unwrap(), 8167); // boundary of large table
    }
}
