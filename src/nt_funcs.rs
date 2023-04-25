//! Standalone number theoretic functions
//!
//! The functions in this module can be called without an instance of [crate::traits::PrimeBuffer].
//! However, some functions do internally call the implementation on [PrimeBufferExt]
//! (especially those dependent of integer factorization). For these functions, if you have
//! to call them repeatedly, it's recommended to create a [crate::traits::PrimeBuffer]
//! instance and use its associated methods for better performance.
//!
//! For number theoretic functions that depends on integer factorization, strongest primality
//! check will be used in factorization, since for these functions we prefer correctness
//! over speed.
//!

use crate::stdlib::collections::BTreeMap;
use crate::stdlib::vec::Vec;
#[cfg(not(feature = "std"))]
use num_traits::float::Float;

use crate::buffer::NaiveBuffer;
use crate::mint::SmallMint;
#[cfg(feature = "big-table")]
use crate::tables::ZETA_LOG_TABLE;
use crate::tables::{SMALL_PRIMES, SMALL_PRIMES_NEXT, WHEEL_NEXT, WHEEL_SIZE};
use crate::traits::PrimalityUtils;
use core::convert::TryFrom;
use num_traits::{FromPrimitive, Num, RefNum, ToPrimitive};

#[cfg(feature = "big-table")]
use crate::tables::{MILLER_RABIN_BASE32, MILLER_RABIN_BASE64};

/// Fast primality test on a u64 integer. It's based on
/// deterministic Miller-rabin tests. If target is larger than 2^64 or more
/// controlled primality tests are desired, please use [is_prime()]
#[cfg(not(feature = "big-table"))]
pub fn is_prime64(target: u64) -> bool {
    // shortcuts
    if target < 2 {
        return false;
    }
    if target & 1 == 0 {
        return target == 2;
    }
    if let Ok(u) = u8::try_from(target) {
        // find in the prime list if the target is small enough
        return SMALL_PRIMES.binary_search(&u).is_ok();
    } else {
        // check remainder against the wheel table
        // this step eliminates any number that is not coprime to WHEEL_SIZE
        let pos = (target % WHEEL_SIZE as u64) as usize;
        if pos == 0 || WHEEL_NEXT[pos] < WHEEL_NEXT[pos - 1] {
            return false;
        }
    }

    // Then do a deterministic Miller-rabin test
    is_prime64_miller(target)
}

/// Very fast primality test on a u64 integer is a prime number. It's based on
/// deterministic Miller-rabin tests with hashing. if target is larger than 2^64 or more controlled
/// primality tests are desired, please use [is_prime()]
#[cfg(feature = "big-table")]
pub fn is_prime64(target: u64) -> bool {
    // shortcuts
    if target < 2 {
        return false;
    }
    if target & 1 == 0 {
        return target == 2;
    }

    // remove small factors
    if target < SMALL_PRIMES_NEXT {
        // find in the prime list if the target is small enough
        return SMALL_PRIMES.binary_search(&(target as u16)).is_ok();
    } else {
        // check remainder against the wheel table
        // this step eliminates any number that is not coprime to WHEEL_SIZE
        let pos = (target % WHEEL_SIZE as u64) as usize;
        if pos == 0 || WHEEL_NEXT[pos] < WHEEL_NEXT[pos - 1] {
            return false;
        }
    }

    // Then do a deterministic Miller-rabin test
    is_prime64_miller(target)
}

// Primality test for u64 with only miller-rabin tests, used during factorization.
// It assumes the target is odd, not too small and cannot be divided small primes
#[cfg(not(feature = "big-table"))]
fn is_prime64_miller(target: u64) -> bool {
    // The collection of witnesses are from http://miller-rabin.appspot.com/
    if let Ok(u) = u32::try_from(target) {
        const WITNESS32: [u32; 3] = [2, 7, 61];
        let u = SmallMint::from(u);
        WITNESS32.iter().all(|&x| u.is_sprp(SmallMint::from(x)))
    } else {
        const WITNESS64: [u64; 7] = [2, 325, 9375, 28178, 450775, 9780504, 1795265022];
        let u = SmallMint::from(target);
        WITNESS64.iter().all(|&x| u.is_sprp(SmallMint::from(x)))
    }
}

#[cfg(feature = "big-table")]
fn is_prime32_miller(target: u32) -> bool {
    let h = target as u64;
    let h = ((h >> 16) ^ h).wrapping_mul(0x45d9f3b);
    let h = ((h >> 16) ^ h).wrapping_mul(0x45d9f3b);
    let h = ((h >> 16) ^ h) & 255;
    let u = SmallMint::from(target);
    return u.is_sprp(SmallMint::from(MILLER_RABIN_BASE32[h as usize] as u32));
}

// Primality test for u64 with only miller-rabin tests, used during factorization.
// It assumes the target is odd, not too small and cannot be divided small primes
#[cfg(feature = "big-table")]
fn is_prime64_miller(target: u64) -> bool {
    if let Ok(u) = u32::try_from(target) {
        return is_prime32_miller(u);
    }

    let u = SmallMint::from(target);
    if !u.is_sprp(2.into()) {
        return false;
    }

    let h = target;
    let h = ((h >> 32) ^ h).wrapping_mul(0x45d9f3b3335b369);
    let h = ((h >> 32) ^ h).wrapping_mul(0x3335b36945d9f3b);
    let h = ((h >> 32) ^ h) & 16383;
    let b = MILLER_RABIN_BASE64[h as usize];
    return u.is_sprp((b as u64 & 4095).into()) && u.is_sprp((b as u64 >> 12).into());
}

/// Get a list of primes under a limit
///
/// This function re-exports [NaiveBuffer::primes()] and collect result as a vector.
pub fn primes(limit: u64) -> Vec<u64> {
    NaiveBuffer::new().into_primes(limit).collect()
}

/// This function calculate the Möbius `μ(n)` function given the factorization
/// result of `n`
pub fn moebius_factorized<T>(factors: &BTreeMap<T, usize>) -> i8 {
    if factors.values().any(|exp| exp > &1) {
        0
    } else if factors.len() % 2 == 0 {
        1
    } else {
        -1
    }
}

/// Returns the estimated bounds (low, high) of prime π function, such that
/// low <= π(target) <= high
///
/// # Reference:
/// - \[1] Dusart, Pierre. "Estimates of Some Functions Over Primes without R.H."
/// [arxiv:1002.0442](http://arxiv.org/abs/1002.0442). 2010.
/// - \[2] Dusart, Pierre. "Explicit estimates of some functions over primes."
/// The Ramanujan Journal 45.1 (2018): 227-251.
pub fn prime_pi_bounds<T: ToPrimitive + FromPrimitive>(target: &T) -> (T, T) {
    if let Some(x) = target.to_u64() {
        // use existing primes and return exact value
        if x <= (*SMALL_PRIMES.last().unwrap()) as u64 {
            #[cfg(not(feature = "big-table"))]
            let pos = SMALL_PRIMES.binary_search(&(x as u8));
            #[cfg(feature = "big-table")]
            let pos = SMALL_PRIMES.binary_search(&(x as u16));

            let n = match pos {
                Ok(p) => p + 1,
                Err(p) => p,
            };
            return (T::from_usize(n).unwrap(), T::from_usize(n).unwrap());
        }

        // use function approximation
        let n = x as f64;
        let ln = n.ln();
        let invln = ln.recip();

        let lo = match () {
            // [2] Collary 5.3
            _ if x >= 468049 => n / (ln - 1. - invln),
            // [2] Collary 5.2
            _ if x >= 88789 => n * invln * (1. + invln * (1. + 2. * invln)),
            // [2] Collary 5.3
            _ if x >= 5393 => n / (ln - 1.),
            // [2] Collary 5.2
            _ if x >= 599 => n * invln * (1. + invln),
            // [2] Collary 5.2
            _ => n * invln,
        };
        let hi = match () {
            // [2] Theorem 5.1, valid for x > 4e9, intersects at 7.3986e9
            _ if x >= 7398600000 => n * invln * (1. + invln * (1. + invln * (2. + invln * 7.59))),
            // [1] Theorem 6.9
            _ if x >= 2953652287 => n * invln * (1. + invln * (1. + invln * 2.334)),
            // [2] Collary 5.3, valid for x > 5.6, intersects at 5668
            _ if x >= 467345 => n / (ln - 1. - 1.2311 * invln),
            // [2] Collary 5.2, valid for x > 1, intersects at 29927
            _ if x >= 29927 => n * invln * (1. + invln * (1. + invln * 2.53816)),
            // [2] Collary 5.3, valid for x > exp(1.112), intersects at 5668
            _ if x >= 5668 => n / (ln - 1.112),
            // [2] Collary 5.2, valid for x > 1, intersects at 148
            _ if x >= 148 => n * invln * (1. + invln * 1.2762),
            // [2] Collary 5.2, valid for x > 1
            _ => 1.25506 * n * invln,
        };
        (T::from_f64(lo).unwrap(), T::from_f64(hi).unwrap())
    } else {
        let n = target.to_f64().unwrap();
        let ln = n.ln();
        let invln = ln.recip();

        // best bounds so far
        let lo = n / (ln - 1. - invln);
        let hi = n * invln * (1. + invln * (1. + invln * (2. + invln * 7.59)));
        (T::from_f64(lo).unwrap(), T::from_f64(hi).unwrap())
    }
}

/// Returns the estimated inclusive bounds (low, high) of the n-th prime. If the result
/// is larger than maximum of `T`, [None] will be returned.
///
/// # Reference:
/// - \[1] Dusart, Pierre. "Estimates of Some Functions Over Primes without R.H."
/// arXiv preprint [arXiv:1002.0442](https://arxiv.org/abs/1002.0442) (2010).
/// - \[2] Rosser, J. Barkley, and Lowell Schoenfeld. "Approximate formulas for some
/// functions of prime numbers." Illinois Journal of Mathematics 6.1 (1962): 64-94.
/// - \[3] Dusart, Pierre. "The k th prime is greater than k (ln k+ ln ln k-1) for k≥ 2."
/// Mathematics of computation (1999): 411-415.
/// - \[4] Axler, Christian. ["New Estimates for the nth Prime Number."](https://www.emis.de/journals/JIS/VOL22/Axler/axler17.pdf)
/// Journal of Integer Sequences 22.2 (2019): 3.
/// - \[5] Axler, Christian. [Uber die Primzahl-Zählfunktion, die n-te Primzahl und verallgemeinerte Ramanujan-Primzahlen. Diss.](http://docserv.uniduesseldorf.de/servlets/DerivateServlet/Derivate-28284/pdfa-1b.pdf)
/// PhD thesis, Düsseldorf, 2013.
///
/// Note that some of the results might depend on the Riemann Hypothesis. If you find
/// any prime that doesn't fall in the bound, then it might be a big discovery!
pub fn nth_prime_bounds<T: ToPrimitive + FromPrimitive>(target: &T) -> Option<(T, T)> {
    if let Some(x) = target.to_usize() {
        if x == 0 {
            return Some((T::from_u8(0).unwrap(), T::from_u8(0).unwrap()));
        }

        // use existing primes and return exact value
        if x <= SMALL_PRIMES.len() {
            let p = SMALL_PRIMES[x - 1];

            #[cfg(not(feature = "big-table"))]
            return Some((T::from_u8(p).unwrap(), T::from_u8(p).unwrap()));

            #[cfg(feature = "big-table")]
            return Some((T::from_u16(p).unwrap(), T::from_u16(p).unwrap()));
        }

        // use function approximation
        let n = x as f64;
        let ln = n.ln();
        let lnln = ln.ln();

        let lo = match () {
            // [4] Theroem 4, valid for x >= 2, intersects as 3.172e5
            _ if x >= 317200 => {
                n * (ln + lnln - 1. + (lnln - 2.) / ln
                    - (lnln * lnln - 6. * lnln + 11.321) / (2. * ln * ln))
            }
            // [1] Proposition 6.7, valid for x >= 3, intersects at 3520
            _ if x >= 3520 => n * (ln + lnln - 1. + (lnln - 2.1) / ln),
            // [3] title
            _ => n * (ln + lnln - 1.),
        };
        let hi = match () {
            // [4] Theroem 1, valid for x >= 46254381
            _ if x >= 46254381 => {
                n * (ln + lnln - 1. + (lnln - 2.) / ln
                    - (lnln * lnln - 6. * lnln + 10.667) / (2. * ln * ln))
            }
            // [5] Korollar 2.11, valid for x >= 8009824
            _ if x >= 8009824 => {
                n * (ln + lnln - 1. + (lnln - 2.) / ln
                    - (lnln * lnln - 6. * lnln + 10.273) / (2. * ln * ln))
            }
            // [1] Proposition 6.6
            _ if x >= 688383 => n * (ln + lnln - 1. + (lnln - 2.) / ln),
            // [1] Lemma 6.5
            _ if x >= 178974 => n * (ln + lnln - 1. + (lnln - 1.95) / ln),
            // [3] in "Further Results"
            _ if x >= 39017 => n * (ln + lnln - 0.9484),
            // [3] in "Further Results"
            _ if x >= 27076 => n * (ln + lnln - 1. + (lnln - 1.8) / ln),
            // [2] Theorem 3, valid for x >= 20
            _ => n * (ln + lnln - 0.5),
        };
        Some((T::from_f64(lo)?, T::from_f64(hi)?))
    } else {
        let n = target.to_f64().unwrap();
        let ln = n.ln();
        let lnln = ln.ln();

        // best bounds so far
        let lo = n
            * (ln + lnln - 1. + (lnln - 2.) / ln
                - (lnln * lnln - 6. * lnln + 11.321) / (2. * ln * ln));
        let hi = n
            * (ln + lnln - 1. + (lnln - 2.) / ln
                - (lnln * lnln - 6. * lnln + 10.667) / (2. * ln * ln));
        Some((T::from_f64(lo)?, T::from_f64(hi)?))
    }
}

/// Estimate the value of prime π() function by averaging the estimated bounds.
#[cfg(not(feature = "big-table"))]
pub fn prime_pi_est<T: Num + ToPrimitive + FromPrimitive>(target: &T) -> T {
    let (lo, hi) = prime_pi_bounds(target);
    (lo + hi) / T::from_u8(2).unwrap()
}

/// Estimate the value of prime π() function by Riemann's R function. The estimation
/// error is roughly of scale O(sqrt(x)log(x)).
///
/// Reference: <https://primes.utm.edu/howmany.html#better>
#[cfg(feature = "big-table")]
pub fn prime_pi_est<T: ToPrimitive + FromPrimitive>(target: &T) -> T {
    // shortcut
    if let Some(x) = target.to_u16() {
        if x <= (*SMALL_PRIMES.last().unwrap()) as u16 {
            let (lo, hi) = prime_pi_bounds(&x);
            debug_assert_eq!(lo, hi);
            return T::from_u16(lo).unwrap();
        }
    }

    // Gram expansion with logarithm arithmetics
    let lnln = target.to_f64().unwrap().ln().ln();
    let mut total = 0f64;
    let mut lnp = 0f64; // k*ln(ln(x))
    let mut lnfac = 0f64; // ln(k!)

    for k in 1usize..100 {
        lnp += lnln;
        let lnk = (k as f64).ln();
        lnfac += lnk;
        let lnzeta = if k > 64 { 0f64 } else { ZETA_LOG_TABLE[k - 1] };
        let t = lnp - lnk - lnfac - lnzeta;
        if t < -4. {
            // stop if the increment is too small
            break;
        }
        total += t.exp();
    }
    T::from_f64(total + 1f64).unwrap()
}

/// Estimate the value of nth prime by bisecting on [prime_pi_est].
/// If the result is larger than maximum of `T`, [None] will be returned.
pub fn nth_prime_est<T: ToPrimitive + FromPrimitive + Num + PartialOrd>(target: &T) -> Option<T>
where
    for<'r> &'r T: RefNum<T>,
{
    let (mut lo, mut hi) = nth_prime_bounds(target)?;
    if lo == hi {
        return Some(lo);
    }

    while lo != &hi - T::from_u8(1).unwrap() {
        let x = (&lo + &hi) / T::from_u8(2).unwrap();
        let mid = prime_pi_est(&x);
        if &mid < target {
            lo = x
        } else if &mid > target {
            hi = x
        } else {
            return Some(x);
        }
    }
    return Some(lo);
}

// TODO: More functions
// REF: http://www.numbertheory.org/gnubc/bc_programs.html
// REF: https://github.com/TilmanNeumann/java-math-library
// - is_smooth: checks if the smoothness bound is at least b
// - euler_phi: Euler's totient function
// - jordan_tot: Jordan's totient function
// Others include Louiville function, Mangoldt function, Dedekind psi function, Dickman rho function, etc..

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{prelude::SliceRandom, random};

    #[test]
    fn is_prime64_test() {
        // test small primes
        for x in 2..100 {
            assert_eq!(SMALL_PRIMES.contains(&x), is_prime64(x as u64));
        }
        assert!(is_prime64(677));

        // from PR #7
        assert!(!is_prime64(9773));
        assert!(!is_prime64(13357));
        assert!(!is_prime64(18769));

        // some large primes
        assert!(is_prime64(6469693333));
        assert!(is_prime64(13756265695458089029));
        assert!(is_prime64(13496181268022124907));
        assert!(is_prime64(10953742525620032441));
        assert!(is_prime64(17908251027575790097));

        // primes from examples in Bradley Berg's hash method
        assert!(is_prime64(480194653));
        assert!(!is_prime64(20074069));
        assert!(is_prime64(8718775377449));
        assert!(is_prime64(3315293452192821991));
        assert!(!is_prime64(8651776913431));
        assert!(!is_prime64(1152965996591997761));

        // false positives reported by JASory (#4)
        assert!(!is_prime64(600437059821397));
        assert!(!is_prime64(3866032210719337));
        assert!(!is_prime64(4100599722623587));

        // ensure no factor for 100 random primes
        let mut rng = rand::thread_rng();
        for _ in 0..100 {
            let x = random();
            if !is_prime64(x) {
                continue;
            }
            assert_ne!(x % (*SMALL_PRIMES.choose(&mut rng).unwrap() as u64), 0);
        }

        // create random composites
        for _ in 0..100 {
            let x = random::<u32>() as u64;
            let y = random::<u32>() as u64;
            assert!(!is_prime64(x * y));
        }
    }

    #[test]
    fn prime_pi_bounds_test() {
        fn check(n: u64, pi: u64) {
            let (lo, hi) = prime_pi_bounds(&n);
            let est = prime_pi_est(&n);
            assert!(
                lo <= pi && pi <= hi,
                "fail to satisfy {} <= pi({}) = {} <= {}",
                lo,
                n,
                pi,
                hi
            );
            assert!(lo <= est && est <= hi);
        }

        // test with sieved primes
        let mut pb = NaiveBuffer::new();
        let mut last = 0;
        for (i, p) in pb.primes(100000).cloned().enumerate() {
            for j in last..p {
                check(j, i as u64);
            }
            last = p;
        }

        // test with some known cases with input as 10^n, OEIS:A006880
        let pow10_values = [
            0,
            4,
            25,
            168,
            1229,
            9592,
            78498,
            664579,
            5761455,
            50847534,
            455052511,
            4118054813,
            37607912018,
            346065536839,
            3204941750802,
            29844570422669,
            279238341033925,
            2623557157654233,
        ];
        for (exponent, gt) in pow10_values.iter().enumerate() {
            let n = 10u64.pow(exponent as u32);
            check(n, *gt);
        }
    }

    #[test]
    fn nth_prime_bounds_test() {
        fn check(n: u64, p: u64) {
            let (lo, hi) = super::nth_prime_bounds(&n).unwrap();
            assert!(
                lo <= p && p <= hi,
                "fail to satisfy: {} <= {}-th prime = {} <= {}",
                lo,
                n,
                p,
                hi
            );
            let est = super::nth_prime_est(&n).unwrap();
            assert!(lo <= est && est <= hi);
        }

        // test with sieved primes
        let mut pb = NaiveBuffer::new();
        for (i, p) in pb.primes(100000).cloned().enumerate() {
            check(i as u64 + 1, p as u64);
        }

        // test with some known cases with input as 10^n, OEIS:A006988
        let pow10_values = [
            2,
            29,
            541,
            7919,
            104729,
            1299709,
            15485863,
            179424673,
            2038074743,
            22801763489,
            252097800623,
            2760727302517,
            29996224275833,
            323780508946331,
            3475385758524527,
            37124508045065437,
        ];
        for (exponent, nth_prime) in pow10_values.iter().enumerate() {
            let n = 10u64.pow(exponent as u32);
            check(n, *nth_prime);
        }
    }
}
