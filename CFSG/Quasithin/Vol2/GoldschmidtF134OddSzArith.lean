module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.H13.NQCore

theorem five_dvd_four_pow_odd_add_one (a : ℕ) : 5 ∣ 4 ^ (2 * a + 1) + 1 := by
  simpa using Odd.nat_add_dvd_pow_add_pow 4 1 (odd_two_mul_add_one a)

theorem four_pow_mod_twentyFour {n : ℕ} (hn : 2 ≤ n) : 4 ^ n % 24 = 16 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

theorem five_pow_mod_twentyFour (j : ℕ) : 5 ^ j % 24 = 1 ∨ 5 ^ j % 24 = 5 := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ]; omega

theorem four_pow_odd_add_one_ne_prime_pow {a j : ℕ} (ha : 1 ≤ a) {p : ℕ} (hp : p.Prime) :
    4 ^ (2 * a + 1) + 1 ≠ p ^ j := by
  intro h
  have h24 : (4 ^ (2 * a + 1) + 1) % 24 = 17 := by
    have := four_pow_mod_twentyFour (n := 2 * a + 1) (by omega)
    omega
  have hj : j ≠ 0 := by
    rintro rfl
    have : 0 < 4 ^ (2 * a + 1) := by positivity
    simp at h
  have h5p : 5 ∣ p :=
    Nat.prime_five.dvd_of_dvd_pow (n := j) (h ▸ five_dvd_four_pow_odd_add_one a)
  obtain rfl : p = 5 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).1 h5p).symm
  rw [h] at h24
  rcases five_pow_mod_twentyFour j with h1 | h1 <;> omega

theorem not_dvd_of_prime_factors {n p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (hn : ∀ r : ℕ, r.Prime → r ∣ n → r = 2 ∨ r = p) :
    ¬ (2 ^ (2 * a + 1)) ^ 2 + 1 ∣ n := by
  intro hdvd
  have hq : (2 ^ (2 * a + 1)) ^ 2 + 1 = 4 ^ (2 * a + 1) + 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [hq] at hdvd
  have hodd : ¬ 2 ∣ 4 ^ (2 * a + 1) + 1 := by
    have h4 : 2 ∣ 4 ^ (2 * a + 1) := dvd_pow (by norm_num) (by omega)
    omega
  have hpow : 4 ^ (2 * a + 1) + 1 = p ^ (4 ^ (2 * a + 1) + 1).primeFactorsList.length := by
    refine Nat.eq_prime_pow_of_unique_prime_dvd (by positivity) fun {d} hd hdd => ?_
    rcases hn d hd (hdd.trans hdvd) with rfl | rfl
    · exact absurd hdd hodd
    · rfl
  exact four_pow_odd_add_one_ne_prime_pow ha hp hpow

end CFSG.Quasithin.H13.NQCore
