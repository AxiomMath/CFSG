module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.SzModel

theorem two_pow_mod_five (m : ℕ) : 2 ^ (2 * m + 1) % 5 = 2 ∨ 2 ^ (2 * m + 1) % 5 = 3 := by
  induction m with
  | zero => simp
  | succ k ih =>
    have : 2 ^ (2 * (k + 1) + 1) = 4 * 2 ^ (2 * k + 1) := by ring
    omega

theorem five_dvd_sq_add_one (m : ℕ) : 5 ∣ (2 ^ (2 * m + 1)) ^ 2 + 1 := by
  have h := two_pow_mod_five m
  have h4 : (2 ^ (2 * m + 1)) ^ 2 % 5 = 4 := by
    rcases h with h | h <;> rw [Nat.pow_mod, h]
  omega

theorem not_five_dvd_two_pow (m : ℕ) : ¬ 5 ∣ 2 ^ (2 * m + 1) := by
  have := two_pow_mod_five m
  generalize 2 ^ (2 * m + 1) = q at *
  omega

theorem not_five_dvd_two_pow_sub_one (m : ℕ) : ¬ 5 ∣ 2 ^ (2 * m + 1) - 1 := by
  have := two_pow_mod_five m
  generalize 2 ^ (2 * m + 1) = q at *
  omega

theorem not_five_dvd_sq_mul_sub_one (m : ℕ) :
    ¬ 5 ∣ (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) := by
  intro hd
  have h5 : Nat.Prime 5 := by norm_num
  rcases h5.dvd_mul.mp hd with h | h
  · exact not_five_dvd_two_pow m (h5.dvd_of_dvd_pow h)
  · exact not_five_dvd_two_pow_sub_one m h

theorem pow_mod_eq_pow_mod_mod {a m n : ℕ} (h : a ^ n % m = 1) (p : ℕ) :
    a ^ p % m = a ^ (p % n) % m := by
  conv_lhs => rw [← Nat.div_add_mod p n, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, h]
  rw [one_pow, Nat.mod_mul_mod, one_mul, Nat.mod_mod]

theorem not_twentyfive_dvd_sq_add_one {m : ℕ} (hp : (2 * m + 1).Prime) (h5 : 2 * m + 1 ≠ 5) :
    ¬ 25 ∣ (2 ^ (2 * m + 1)) ^ 2 + 1 := by
  have hp5 : (2 * m + 1) % 5 ≠ 0 := fun h =>
    h5 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp (Nat.dvd_of_mod_eq_zero h)).symm
  have hmod : (2 ^ (2 * m + 1)) ^ 2 % 25 = 4 ^ ((2 * m + 1) % 10) % 25 := by
    rw [← pow_mul, mul_comm, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num,
      pow_mod_eq_pow_mod_mod (n := 10) (by norm_num)]
  have h10 : (2 * m + 1) % 10 = 1 ∨ (2 * m + 1) % 10 = 3 ∨ (2 * m + 1) % 10 = 7 ∨
      (2 * m + 1) % 10 = 9 := by omega
  intro hd
  rcases h10 with h | h | h | h <;> rw [h] at hmod <;> omega

theorem not_twentyfive_dvd_card {m : ℕ} (hp : (2 * m + 1).Prime) (h5 : 2 * m + 1 ≠ 5) :
    ¬ 25 ∣ (2 ^ (2 * m + 1)) ^ 2 * ((2 ^ (2 * m + 1)) ^ 2 + 1) * (2 ^ (2 * m + 1) - 1) := by
  intro hd
  have h5p : Nat.Prime 5 := by norm_num
  have c1 : Nat.Coprime 25 ((2 ^ (2 * m + 1)) ^ 2) := by
    have := (Nat.Prime.coprime_iff_not_dvd h5p).mpr (not_five_dvd_two_pow m)
    simpa using this.pow 2 2
  have c2 : Nat.Coprime 25 (2 ^ (2 * m + 1) - 1) := by
    have := (Nat.Prime.coprime_iff_not_dvd h5p).mpr (not_five_dvd_two_pow_sub_one m)
    simpa using this.pow_left 2
  exact not_twentyfive_dvd_sq_add_one hp h5 (c1.dvd_of_dvd_mul_left (c2.dvd_of_dvd_mul_right hd))

end CFSG.SignalizerFunctorTheorem.McBride.SzModel
