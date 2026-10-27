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
public import Mathlib.Data.Int.Star
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

namespace CFSG.RankThree.PartTwo.Sec11.R2No

theorem int_cube_dvd (x : ℤ) (k : ℕ) (hx : (3 : ℤ) ^ (k + 1) ∣ x - 1) :
    (3 : ℤ) ^ (k + 2) ∣ x ^ 3 - 1 := by
  obtain ⟨t, ht⟩ := hx
  have hx' : x = 1 + 3 ^ (k + 1) * t := by linarith
  subst hx'
  exact ⟨t * (1 + 3 ^ (k + 1) * t + 3 ^ (2 * k + 1) * t ^ 2), by ring⟩

theorem pow_three_pow_modEq {ν : ℕ} (h : ν % 3 = 1) (m : ℕ) :
    ν ^ 3 ^ m ≡ 1 [MOD 3 ^ (m + 1)] := by
  induction m with
  | zero =>
    simpa [Nat.ModEq] using h
  | succ m ih =>
    have h1 : (3 : ℤ) ^ (m + 1) ∣ ((ν ^ 3 ^ m : ℕ) : ℤ) - 1 := by
      have := (Nat.modEq_iff_dvd.mp ih.symm)
      simpa using this
    have h2 := int_cube_dvd _ m h1
    have h3 : ν ^ 3 ^ (m + 1) = (ν ^ 3 ^ m) ^ 3 := by
      rw [pow_succ 3 m, pow_mul]
    refine (Nat.modEq_iff_dvd.mpr ?_).symm
    rw [h3]
    push_cast
    simpa using h2

theorem geom_sum_three_mul (ν a : ℕ) :
    ∑ k ∈ Finset.range (3 * a), ν ^ k =
      (∑ k ∈ Finset.range a, ν ^ k) * (1 + ν ^ a + ν ^ (2 * a)) := by
  have e : 3 * a = a + (a + a) := by ring
  rw [e, Finset.sum_range_add, Finset.sum_range_add]
  have h1 : ∑ x ∈ Finset.range a, ν ^ (a + (a + x)) =
      ν ^ (2 * a) * ∑ k ∈ Finset.range a, ν ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← pow_add]
    congr 1
    ring
  have h2 : ∑ x ∈ Finset.range a, ν ^ (a + x) = ν ^ a * ∑ k ∈ Finset.range a, ν ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← pow_add]
  rw [h1, h2]
  ring

theorem geom_sum_three_pow_modEq {ν : ℕ} (h : ν % 3 = 1) (m : ℕ) :
    ∑ k ∈ Finset.range (3 ^ m), ν ^ k ≡ 3 ^ m [MOD 3 ^ (m + 1)] := by
  induction m with
  | zero => simpa [Nat.ModEq] using h
  | succ m ih =>
    have hsplit : ∑ k ∈ Finset.range (3 ^ (m + 1)), ν ^ k =
        (∑ k ∈ Finset.range (3 ^ m), ν ^ k) * (1 + ν ^ 3 ^ m + ν ^ (2 * 3 ^ m)) := by
      rw [pow_succ', geom_sum_three_mul]
    rw [hsplit]
    obtain ⟨t, ht⟩ : ∃ t : ℤ, ((∑ k ∈ Finset.range (3 ^ m), ν ^ k : ℕ) : ℤ) =
        3 ^ m + 3 ^ (m + 1) * t := by
      have := Nat.modEq_iff_dvd.mp ih.symm
      obtain ⟨t, ht⟩ := this
      exact ⟨t, by push_cast at ht ⊢; linarith⟩
    have hμ := pow_three_pow_modEq h m
    obtain ⟨s, hs⟩ : ∃ s : ℤ, ((ν ^ 3 ^ m : ℕ) : ℤ) = 1 + 3 ^ (m + 1) * s := by
      have := Nat.modEq_iff_dvd.mp hμ.symm
      obtain ⟨s, hs⟩ := this
      exact ⟨s, by push_cast at hs ⊢; linarith⟩
    refine (Nat.modEq_iff_dvd.mpr ?_).symm
    have hsq : ((ν ^ (2 * 3 ^ m) : ℕ) : ℤ) = ((ν ^ 3 ^ m : ℕ) : ℤ) ^ 2 := by
      rw [two_mul, pow_add]; push_cast; ring
    push_cast at ht hs hsq ⊢
    rw [ht, hsq, hs]
    exact ⟨t * (1 + 3 ^ (m + 1) * s + 3 ^ (2 * m + 1) * s ^ 2) + 3 ^ m * s + 3 ^ (2 * m) * s ^ 2,
      by ring⟩

theorem three_pow_mul_modEq {ν : ℕ} (h : ν % 3 = 1) (m : ℕ) :
    3 ^ m * ν ≡ 3 ^ m [MOD 3 ^ (m + 1)] := by
  have h3 : 3 ∣ ν - 1 := by omega
  obtain ⟨t, ht⟩ := h3
  have hν : ν = 1 + 3 * t := by omega
  subst hν
  refine (Nat.modEq_iff_dvd.mpr ?_).symm
  push_cast
  exact ⟨t, by ring⟩

end CFSG.RankThree.PartTwo.Sec11.R2No
