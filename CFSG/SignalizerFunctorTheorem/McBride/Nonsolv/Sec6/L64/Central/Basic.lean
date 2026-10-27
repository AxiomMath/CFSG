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
public import Mathlib.GroupTheory.IsPerfect
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

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.PerfectCentral

variable {Γ : Type*} [Group Γ]

theorem le_normalizer_of_conj_mem {A M : Subgroup Γ}
    (h : ∀ a ∈ A, ∀ x ∈ M, a * x * a⁻¹ ∈ M) : A ≤ Subgroup.normalizer (M : Set Γ) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  refine fun x => ⟨fun hx => h a ha x hx, fun hx => ?_⟩
  simpa [mul_assoc] using h a⁻¹ (inv_mem ha) _ hx

theorem commutatorElement_mul_mul {z₁ z₂ s₁ s₂ : Γ} (h11 : Commute z₁ s₁) (h12 : Commute z₁ s₂)
    (h21 : Commute z₂ s₁) (h22 : Commute z₂ s₂) (hzz : Commute z₁ z₂) :
    ⁅z₁ * s₁, z₂ * s₂⁆ = ⁅s₁, s₂⁆ := by
  have e1 : z₁ * (s₁ * z₂ * s₂ * s₁⁻¹) * z₁⁻¹ = s₁ * z₂ * s₂ * s₁⁻¹ := by
    have hc : Commute z₁ (s₁ * z₂ * s₂ * s₁⁻¹) :=
      ((h11.mul_right hzz).mul_right h12).mul_right h11.inv_right
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  have e2 : z₂ * (s₁ * s₂ * s₁⁻¹ * s₂⁻¹) * z₂⁻¹ = s₁ * s₂ * s₁⁻¹ * s₂⁻¹ := by
    have hc : Commute z₂ (s₁ * s₂ * s₁⁻¹ * s₂⁻¹) :=
      ((h21.mul_right h22).mul_right h21.inv_right).mul_right h22.inv_right
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  simp only [commutatorElement_def, mul_inv_rev]
  calc z₁ * s₁ * (z₂ * s₂) * (s₁⁻¹ * z₁⁻¹) * (s₂⁻¹ * z₂⁻¹)
      = (z₁ * (s₁ * z₂ * s₂ * s₁⁻¹) * z₁⁻¹) * s₂⁻¹ * z₂⁻¹ := by group
    _ = (s₁ * z₂ * s₂ * s₁⁻¹) * s₂⁻¹ * z₂⁻¹ := by rw [e1]
    _ = z₂ * (s₁ * s₂ * s₁⁻¹ * s₂⁻¹) * z₂⁻¹ := by rw [← h21.eq]; group
    _ = s₁ * s₂ * s₁⁻¹ * s₂⁻¹ := e2

theorem commutator_le_of_forall_mul {W Z P S : Subgroup Γ} (hZW : Z ≤ W) (hSW : S ≤ W)
    (hZc : ∀ z ∈ Z, ∀ w ∈ W, z * w = w * z)
    (hPS : ∀ x ∈ P, ∃ z ∈ Z, ∃ s ∈ S, x = z * s) : ⁅P, P⁆ ≤ ⁅S, S⁆ := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨z₁, hz₁, s₁, hs₁, rfl⟩ := hPS g₁ hg₁
  obtain ⟨z₂, hz₂, s₂, hs₂, rfl⟩ := hPS g₂ hg₂
  rw [commutatorElement_mul_mul (hZc z₁ hz₁ s₁ (hSW hs₁)) (hZc z₁ hz₁ s₂ (hSW hs₂))
    (hZc z₂ hz₂ s₁ (hSW hs₁)) (hZc z₂ hz₂ s₂ (hSW hs₂)) (hZc z₁ hz₁ z₂ (hZW hz₂))]
  exact Subgroup.commutator_mem_commutator hs₁ hs₂

theorem commutator_self_eq_of_isSimpleGroup {J : Subgroup Γ} [IsSimpleGroup J]
    (hnc : ∃ x ∈ J, ∃ y ∈ J, x * y ≠ y * x) : ⁅J, J⁆ = J := by
  have hperf : Group.IsPerfect J := by
    rw [Group.isPerfect_def]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator J) with h | h
    · exfalso
      obtain ⟨x, hx, y, hy, hxy⟩ := hnc
      refine hxy ?_
      have hmem : ⁅(⟨x, hx⟩ : J), ⟨y, hy⟩⁆ ∈ commutator J :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact congrArg Subtype.val hmem
    · exact h
  exact Subgroup.isPerfect_iff.mp hperf

theorem card_map_eq_of_injOn {H : Type*} [Group H] {f : Γ →* H} {S : Subgroup Γ}
    (h : Set.InjOn f S) : Nat.card (S.map f) = Nat.card S := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun s : S => (⟨f s, Subgroup.mem_map_of_mem f s.2⟩ : S.map f)) ⟨?_, ?_⟩)).symm
  · intro s t hst
    exact Subtype.ext (h s.2 t.2 (congrArg Subtype.val hst))
  · rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem map_inf_comap {H : Type*} [Group H] (f : Γ →* H) (W : Subgroup Γ) (J : Subgroup H) :
    (W ⊓ J.comap f).map f = W.map f ⊓ J := by
  ext x
  constructor
  · rintro ⟨w, ⟨hw, hwJ⟩, rfl⟩
    exact ⟨⟨w, hw, rfl⟩, hwJ⟩
  · rintro ⟨⟨w, hw, rfl⟩, hJ⟩
    exact ⟨w, ⟨hw, hJ⟩, rfl⟩

theorem mk'_eq_one_iff {Z : Subgroup Γ} [Z.Normal] {x : Γ} :
    QuotientGroup.mk' Z x = 1 ↔ x ∈ Z := by
  rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']

theorem mem_of_mk'_eq {Z : Subgroup Γ} [Z.Normal] {x y : Γ}
    (h : QuotientGroup.mk' Z x = QuotientGroup.mk' Z y) : x * y⁻¹ ∈ Z := by
  rw [← mk'_eq_one_iff, map_mul, map_inv, h, mul_inv_cancel]

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.PerfectCentral
