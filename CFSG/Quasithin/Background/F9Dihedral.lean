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

namespace CFSG.Quasithin.F9Dihedral

variable {Γ : Type*} [Group Γ]

theorem mul_zpow_eq {a b : Γ} (ha : a * a = 1) (hb : b * b = 1) (k : ℤ) :
    a * (a * b) ^ k = (a * b) ^ (-k) * a ∧ b * (a * b) ^ k = (a * b) ^ (-k) * b := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hinv : (a * b)⁻¹ = b * a := by rw [mul_inv_rev, ha', hb']
  have h1 : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
    rw [hinv, ha']
    calc a * (a * b) * a = (a * a) * b * a := by group
      _ = b * a := by rw [ha, one_mul]
  have h2 : b * (a * b) * b⁻¹ = (a * b)⁻¹ := by
    rw [hinv, hb']
    calc b * (a * b) * b = b * a * (b * b) := by group
      _ = b * a := by rw [hb, mul_one]
  refine ⟨?_, ?_⟩
  · have h3 := conj_zpow (a := a) (b := a * b) (i := k)
    rw [h1, inv_zpow', ha'] at h3
    calc a * (a * b) ^ k = a * (a * b) ^ k * (a * a) := by rw [ha, mul_one]
      _ = (a * (a * b) ^ k * a) * a := (mul_assoc _ _ _).symm
      _ = (a * b) ^ (-k) * a := by rw [← h3]
  · have h3 := conj_zpow (a := b) (b := a * b) (i := k)
    rw [h2, inv_zpow', hb'] at h3
    calc b * (a * b) ^ k = b * (a * b) ^ k * (b * b) := by rw [hb, mul_one]
      _ = (b * (a * b) ^ k * b) * b := (mul_assoc _ _ _).symm
      _ = (a * b) ^ (-k) * b := by rw [← h3]

theorem mem_closure_pair {a b : Γ} (ha : a * a = 1) (hb : b * b = 1) {w : Γ}
    (hw : w ∈ Subgroup.closure ({a, b} : Set Γ)) :
    ∃ k : ℤ, w = (a * b) ^ k ∨ w = (a * b) ^ k * a := by
  have key : ∀ k : ℤ, a * (a * b) ^ k = (a * b) ^ (-k) * a := fun k => (mul_zpow_eq ha hb k).1
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ⟨0, Or.inr (by simp)⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      refine ⟨-1, Or.inr ?_⟩
      rw [zpow_neg_one, mul_inv_rev, ha', hb', mul_assoc, ha, mul_one]
  | one => exact ⟨0, Or.inl (by simp)⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨k, hk⟩ := ihx
    obtain ⟨l, hl⟩ := ihy
    rcases hk with rfl | rfl <;> rcases hl with rfl | rfl
    · exact ⟨k + l, Or.inl (zpow_add _ _ _).symm⟩
    · exact ⟨k + l, Or.inr (by rw [zpow_add, mul_assoc])⟩
    · refine ⟨k - l, Or.inr ?_⟩
      rw [mul_assoc, key l, ← mul_assoc, ← zpow_add, sub_eq_add_neg]
    · refine ⟨k - l, Or.inl ?_⟩
      calc (a * b) ^ k * a * ((a * b) ^ l * a)
          = (a * b) ^ k * (a * (a * b) ^ l) * a := by group
        _ = (a * b) ^ k * ((a * b) ^ (-l) * a) * a := by rw [key l]
        _ = (a * b) ^ k * (a * b) ^ (-l) * (a * a) := by group
        _ = (a * b) ^ (k - l) := by rw [ha, mul_one, ← zpow_add, sub_eq_add_neg]
  | inv x _ ihx =>
    obtain ⟨k, hk⟩ := ihx
    rcases hk with rfl | rfl
    · exact ⟨-k, Or.inl (zpow_neg _ _).symm⟩
    · refine ⟨k, Or.inr ?_⟩
      rw [mul_inv_rev, ha', ← zpow_neg, key (-k), neg_neg]

theorem exists_conj_eq_mul_zpow {a b : Γ} (ha : a * a = 1) (hb : b * b = 1) (k : ℤ) :
    ∃ s : ℤ, ((a * b) ^ s)⁻¹ * a * (a * b) ^ s = a * (a * b) ^ k ∨
      ((a * b) ^ s)⁻¹ * b * (a * b) ^ s = a * (a * b) ^ k := by
  obtain ⟨s, rfl | rfl⟩ := Int.even_or_odd' k
  · refine ⟨s, Or.inl ?_⟩
    have h1 := (mul_zpow_eq ha hb s).1
    have h2 := (mul_zpow_eq ha hb (2 * s)).1
    rw [mul_assoc, h1, ← mul_assoc, ← zpow_neg, ← zpow_add, h2, ← two_mul, neg_mul_eq_mul_neg]
  · refine ⟨s, Or.inr ?_⟩
    have h1 := (mul_zpow_eq ha hb s).2
    have h2 := (mul_zpow_eq ha hb (2 * s)).2
    have h3 : a * (a * b) ^ (2 * s + 1) = b * (a * b) ^ (2 * s) := by
      rw [add_comm (2 * s) 1, zpow_one_add, ← mul_assoc, ← mul_assoc, ha, one_mul]
    rw [mul_assoc, h1, ← mul_assoc, ← zpow_neg, ← zpow_add, h3, h2, ← two_mul, neg_mul_eq_mul_neg]

theorem zpow_mul_mul_notMem {N : Subgroup Γ} [N.Normal] {a b : Γ} (ha : a * a ∈ N)
    (hb : b * b ∈ N) (ha1 : a ∉ N) (hb1 : b ∉ N) (k : ℤ) : (a * b) ^ k * a ∉ N := by
  intro hk
  set A : Γ ⧸ N := (a : Γ ⧸ N) with hA
  set B : Γ ⧸ N := (b : Γ ⧸ N) with hB
  have hAA : A * A = 1 := by
    rw [hA, ← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff _).mpr ha
  have hBB : B * B = 1 := by
    rw [hB, ← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff _).mpr hb
  have hA1 : A ≠ 1 := fun h => ha1 ((QuotientGroup.eq_one_iff _).mp h)
  have hB1 : B ≠ 1 := fun h => hb1 ((QuotientGroup.eq_one_iff _).mp h)
  have hk1 : (A * B) ^ k * A = 1 := by
    have := (QuotientGroup.eq_one_iff _).mpr hk
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow, QuotientGroup.mk_mul] at this
    exact this
  have hA' : A⁻¹ = A := inv_eq_of_mul_eq_one_right hAA
  have h1 : (A * B) ^ k = A := by
    have := eq_inv_of_mul_eq_one_left hk1
    rwa [hA'] at this
  have hc : Commute (A * B) A := by
    have := Commute.self_zpow (A * B) k
    rwa [h1] at this
  have hab : A * B = B * A := by
    have h2 : A * B * A = A * (A * B) := hc.eq
    have h3 : A * B * A = B := by
      calc A * B * A = A * (A * B) := h2
        _ = (A * A) * B := by group
        _ = B := by rw [hAA, one_mul]
    calc A * B = A * B * (A * A) := by rw [hAA, mul_one]
      _ = (A * B * A) * A := by group
      _ = B * A := by rw [h3]
  have hsq : (A * B) * (A * B) = 1 := by
    calc (A * B) * (A * B) = A * (B * A) * B := by group
      _ = A * (A * B) * B := by rw [← hab]
      _ = (A * A) * (B * B) := by group
      _ = 1 := by rw [hAA, hBB, one_mul]
  have h4 : (A * B) ^ k = 1 ∨ (A * B) ^ k = A * B := by
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · left
      rw [zpow_mul, zpow_two, hsq, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul, zpow_two, hsq, one_zpow, one_mul]
  rcases h4 with h4 | h4
  · rw [h1] at h4
    exact hA1 h4
  · rw [h1] at h4
    exact hB1 (mul_eq_left.mp h4.symm)

end CFSG.Quasithin.F9Dihedral
