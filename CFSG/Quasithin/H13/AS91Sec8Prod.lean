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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.H13.AS91

open scoped Pointwise

theorem card_mul_set_mul_card_inf {G : Type*} [Group G] [Finite G] (A B : Subgroup G) :
    Nat.card ((A : Set G) * (B : Set G)) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have hstab : MulAction.stabilizer A (QuotientGroup.mk (1 : G) : G ⧸ B) = B.subgroupOf A := by
    ext s
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    show QuotientGroup.mk ((s : G) * 1) = (QuotientGroup.mk (1 : G) : G ⧸ B) ↔ (s : G) ∈ B
    rw [QuotientGroup.eq]
    simp
  have horb : MulAction.orbit A (QuotientGroup.mk (1 : G) : G ⧸ B) =
      QuotientGroup.mk '' (A : Set G) := by
    ext y
    constructor
    · intro hy
      obtain ⟨s, rfl⟩ := MulAction.mem_orbit_iff.mp hy
      refine ⟨(s : G), s.2, ?_⟩
      show QuotientGroup.mk (s : G) = QuotientGroup.mk ((s : G) * 1)
      rw [mul_one]
    · rintro ⟨g, hg, rfl⟩
      refine MulAction.mem_orbit_iff.mpr ⟨⟨g, hg⟩, ?_⟩
      show QuotientGroup.mk (g * 1) = QuotientGroup.mk g
      rw [mul_one]
  have h2 : Nat.card ↑(QuotientGroup.mk '' (A : Set G) : Set (G ⧸ B)) = B.relIndex A := by
    rw [Nat.card_coe_set_eq, ← horb, ← MulAction.index_stabilizer, hstab]
    rfl
  have h3 := Subgroup.card_mul_eq_card_subgroup_mul_card_quotient B (A : Set G)
  have h4 := Subgroup.relIndex_mul_card B A
  rw [inf_comm] at h4
  rw [h3, h2, mul_assoc, h4, mul_comm]

theorem coe_sup_eq_mul_of_normalizes {G : Type*} [Group G] (A B : Subgroup G)
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B) :
    ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) := by
  apply Subgroup.coe_mul_of_left_le_normalizer_right A B
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact h a ha x
  · intro hx
    have := h a⁻¹ (A.inv_mem ha) _ hx
    simpa [mul_assoc] using this

theorem exists_mul_of_card_eq {G : Type*} [Group G] [Finite G] (A B R : Subgroup G) (hA : A ≤ R)
    (hB : B ≤ R) (h : Nat.card ↥A * Nat.card ↥B = Nat.card ↥R * Nat.card ↥(A ⊓ B)) :
    ∀ r ∈ R, ∃ a ∈ A, ∃ b ∈ B, a * b = r := by
  intro r hr
  have hk : 0 < Nat.card ↥(A ⊓ B) := by
    haveI : Nonempty ↥(A ⊓ B) := ⟨1⟩
    exact Nat.card_pos
  have h1 := card_mul_set_mul_card_inf A B
  have hsub : (A : Set G) * (B : Set G) ⊆ (R : Set G) := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact R.mul_mem (hA ha) (hB hb)
  have hcard : Nat.card ↑((A : Set G) * (B : Set G)) = Nat.card ↥R := by
    apply Nat.eq_of_mul_eq_mul_right hk
    rw [h1, h]
  have heq : (A : Set G) * (B : Set G) = (R : Set G) := by
    apply Set.eq_of_subset_of_ncard_le hsub
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact hcard.ge
  have hr' : r ∈ (A : Set G) * (B : Set G) := by
    rw [heq]
    exact hr
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hr'
  exact ⟨a, ha, b, hb, hab⟩

end CFSG.Quasithin.H13.AS91
