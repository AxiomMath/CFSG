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

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.PSL2Even

theorem two_pow_mod_three {p : ℕ} (hp : Odd p) : 2 ^ p % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hp
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem two_pow_mod_nine (p : ℕ) : 2 ^ p % 9 = 2 ^ (p % 6) % 9 := by
  conv_lhs => rw [← Nat.div_add_mod p 6, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem not_three_dvd_pow_sub_one {p : ℕ} (hp : Odd p) : ¬ 3 ∣ 2 ^ p - 1 := by
  have h := two_pow_mod_three hp
  have : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  omega

theorem three_dvd_pow_add_one {p : ℕ} (hp : Odd p) : 3 ∣ 2 ^ p + 1 := by
  have h := two_pow_mod_three hp
  omega

theorem not_three_dvd_pow {p : ℕ} (hp : Odd p) : ¬ 3 ∣ 2 ^ p := by
  have h := two_pow_mod_three hp
  omega

theorem not_nine_dvd_pow_add_one {p : ℕ} (hp : p.Prime) (hodd : Odd p) (h3 : p ≠ 3) :
    ¬ 9 ∣ 2 ^ p + 1 := by
  have h6 : p % 6 = 1 ∨ p % 6 = 5 := by
    have h2 : p % 2 = 1 := Nat.odd_iff.mp hodd
    have h3' : p % 3 ≠ 0 := fun h => h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.dvd_of_mod_eq_zero h)).symm
    omega
  have h9 := two_pow_mod_nine p
  rcases h6 with h | h <;> rw [h] at h9 <;> norm_num at h9 <;> omega

theorem not_nine_dvd_card {p : ℕ} (hp : p.Prime) (hodd : Odd p) (h3 : p ≠ 3) :
    ¬ 9 ∣ 2 ^ p * ((2 ^ p) ^ 2 - 1) := by
  intro h
  have hfac : (2 ^ p) ^ 2 - 1 = (2 ^ p + 1) * (2 ^ p - 1) := by
    rw [← Nat.sq_sub_sq, one_pow]
  have h' : 9 ∣ (2 ^ p + 1) * (2 ^ p * (2 ^ p - 1)) := by
    rw [hfac] at h
    convert h using 1
    ring
  have hcop : Nat.Coprime 9 (2 ^ p * (2 ^ p - 1)) := by
    have h1 : Nat.Coprime 3 (2 ^ p) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (not_three_dvd_pow hodd)
    have h2 : Nat.Coprime 3 (2 ^ p - 1) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (not_three_dvd_pow_sub_one hodd)
    exact Nat.Coprime.pow_left 2 (h1.mul_right h2)
  exact not_nine_dvd_pow_add_one hp hodd h3 (hcop.dvd_of_dvd_mul_right h')

theorem not_five_dvd {p : ℕ} (hp : Odd p) : ¬ 5 ∣ 2 ^ (2 * p) - 1 := by
  obtain ⟨k, rfl⟩ := hp
  have h1 : 2 ^ (2 * (2 * k + 1)) % 5 = 4 := by
    rw [mul_add, mul_one, pow_add, pow_mul, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have : 1 ≤ 2 ^ (2 * (2 * k + 1)) := Nat.one_le_two_pow
  omega

theorem not_sixteen_dvd {p : ℕ} (hp : 0 < p) : ¬ 16 ∣ 2 ^ (2 * p) - 1 := by
  have h : 2 ^ (2 * p) = 2 * 2 ^ (2 * p - 1) := by
    rw [← pow_succ']; congr 1; omega
  have : 1 ≤ 2 ^ (2 * p - 1) := Nat.one_le_two_pow
  omega

theorem odd_two_pow_sub_one {p : ℕ} (hp : 0 < p) : Odd (2 ^ p - 1) := by
  have h : 2 ^ p = 2 * 2 ^ (p - 1) := by
    rw [← pow_succ']; congr 1; omega
  have : 1 ≤ 2 ^ (p - 1) := Nat.one_le_two_pow
  exact ⟨2 ^ (p - 1) - 1, by omega⟩

theorem odd_two_pow_add_one {p : ℕ} (hp : 0 < p) : Odd (2 ^ p + 1) := by
  have h : 2 ^ p = 2 * 2 ^ (p - 1) := by
    rw [← pow_succ']; congr 1; omega
  exact ⟨2 ^ (p - 1), by omega⟩

theorem eq_zero_of_odd_two_pow {m : ℕ} (h : Odd (2 ^ m)) : m = 0 := by
  by_contra hm
  exact (Nat.not_even_iff_odd.mpr h) (by rw [Nat.even_pow]; exact ⟨even_two, hm⟩)

end CFSG.SignalizerFunctorTheorem.McBride.PSL2Even
