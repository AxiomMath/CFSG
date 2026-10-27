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

namespace CFSG.SignalizerFunctorTheorem.McBride.PSL2Three

theorem three_pow_mod_eight {p : ℕ} (hp : Odd p) : 3 ^ p % 8 = 3 := by
  obtain ⟨k, rfl⟩ := hp
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem three_pow_mod_four {p : ℕ} (hp : Odd p) : 3 ^ p % 4 = 3 := by
  have := three_pow_mod_eight hp
  omega

theorem odd_three_pow (p : ℕ) : Odd (3 ^ p) := Odd.pow (by decide)

theorem le_three_pow {p : ℕ} (hp : 3 ≤ p) : 27 ≤ 3 ^ p := by
  calc 27 = 3 ^ 3 := by norm_num
    _ ≤ 3 ^ p := Nat.pow_le_pow_right (by norm_num) hp

theorem odd_three_pow_sub_one_div_two {p : ℕ} (hp : Odd p) : Odd ((3 ^ p - 1) / 2) := by
  have := three_pow_mod_four hp
  have h1 : 1 ≤ 3 ^ p := Nat.one_le_pow _ _ (by norm_num)
  exact ⟨(3 ^ p - 1) / 4, by omega⟩

theorem not_three_dvd_three_pow_add_one {p : ℕ} (hp : 0 < p) : ¬ 3 ∣ 3 ^ p + 1 := by
  intro h
  have h3 : 3 ∣ 3 ^ p := dvd_pow_self 3 hp.ne'
  have := (Nat.dvd_add_right h3).mp h
  omega

theorem not_three_dvd_three_pow_sub_one {p : ℕ} (hp : 0 < p) : ¬ 3 ∣ 3 ^ p - 1 := by
  intro h
  have h3 : 3 ∣ 3 ^ p := dvd_pow_self 3 hp.ne'
  have h1 : 1 ≤ 3 ^ p := Nat.one_le_pow _ _ (by norm_num)
  omega

theorem three_pow_two_mul_mod_sixteen {p : ℕ} (hp : Odd p) : 3 ^ (2 * p) % 16 = 9 := by
  obtain ⟨k, rfl⟩ := hp
  have h : 81 ^ k % 16 = 1 := by rw [Nat.pow_mod]; norm_num
  rw [show 2 * (2 * k + 1) = 2 + 4 * k by ring, pow_add, pow_mul, Nat.mul_mod,
    show (3 : ℕ) ^ 4 = 81 by norm_num, h]
  norm_num

theorem not_sixteen_dvd {p : ℕ} (hp : Odd p) : ¬ 16 ∣ 3 ^ (2 * p) - 1 := by
  have := three_pow_two_mul_mod_sixteen hp
  have h1 : 1 ≤ 3 ^ (2 * p) := Nat.one_le_pow _ _ (by norm_num)
  omega

theorem three_pow_two_mul_mod_five {p : ℕ} (hp : Odd p) : 3 ^ (2 * p) % 5 = 4 := by
  obtain ⟨k, rfl⟩ := hp
  have h : 81 ^ k % 5 = 1 := by rw [Nat.pow_mod]; norm_num
  rw [show 2 * (2 * k + 1) = 2 + 4 * k by ring, pow_add, pow_mul, Nat.mul_mod,
    show (3 : ℕ) ^ 4 = 81 by norm_num, h]
  norm_num

theorem not_five_dvd {p : ℕ} (hp : Odd p) : ¬ 5 ∣ 3 ^ (2 * p) - 1 := by
  have := three_pow_two_mul_mod_five hp
  have h1 : 1 ≤ 3 ^ (2 * p) := Nat.one_le_pow _ _ (by norm_num)
  omega

theorem card_formula_eq (p : ℕ) :
    3 ^ p * ((3 ^ p) ^ 2 - 1) / 2 = 3 ^ p * ((3 ^ p - 1) / 2) * (3 ^ p + 1) := by
  have h1 : 1 ≤ 3 ^ p := Nat.one_le_pow _ _ (by norm_num)
  have h2 : 2 ∣ 3 ^ p - 1 := by
    have := (odd_three_pow p)
    obtain ⟨k, hk⟩ := this
    exact ⟨k, by omega⟩
  obtain ⟨c, hc⟩ := h2
  have h3 : 3 ^ p = 2 * c + 1 := by omega
  rw [hc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  have : (3 ^ p) ^ 2 - 1 = 2 * c * (3 ^ p + 1) := by
    have : (3 ^ p) ^ 2 = (2 * c + 1) ^ 2 := by rw [h3]
    rw [this, h3]
    have : (2 * c + 1) ^ 2 = 2 * c * (2 * c + 1 + 1) + 1 := by ring
    omega
  rw [this]
  rw [show 3 ^ p * (2 * c * (3 ^ p + 1)) = 2 * (3 ^ p * c * (3 ^ p + 1)) by ring,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

end CFSG.SignalizerFunctorTheorem.McBride.PSL2Three
