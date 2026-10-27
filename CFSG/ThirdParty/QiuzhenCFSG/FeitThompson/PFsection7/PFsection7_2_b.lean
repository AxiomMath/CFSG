module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_7_11
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_2_a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_1

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section7

universe v
universe u

@[expose] public def theorem_7_2_b_statement
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (hAL : ∀ a ∈ A, a ∈ L) : Prop :=
  hypothesis_7_1_statement A L H →
    ∀ χ : Section1.ClassFunction G,
      Section1.IsClassFunction χ →
        Section5.cfNormSq (dadeProjectionOn A L H χ) ≤ Section5.cfNormSq χ ∧
          (Section5.cfNormSq (dadeProjectionOn A L H χ) = Section5.cfNormSq χ ↔
            ∃ α : Section1.ClassFunction L,
              Section2.CFOn L A α ∧
                χ = Section2.dadeTransform H hAL α)

/-- Peterfalvi `(7.3)`. -/


private theorem scalarProduct_add_right_pf72
    {G : Type*} [Group G] [Finite G]
    (φ ψ η : Section1.ClassFunction G) :
    Section1.scalarProduct G φ (ψ + η) =
      Section1.scalarProduct G φ ψ + Section1.scalarProduct G φ η := by
  simp [Section1.scalarProduct, mul_add, Finset.sum_add_distrib]


private theorem scalarProduct_sub_right_pf72
    {G : Type*} [Group G] [Finite G]
    (φ ψ η : Section1.ClassFunction G) :
    Section1.scalarProduct G φ (ψ - η) =
      Section1.scalarProduct G φ ψ - Section1.scalarProduct G φ η := by
  rw [sub_eq_add_neg, scalarProduct_add_right_pf72]
  have hneg : Section1.scalarProduct G φ (-η) = -Section1.scalarProduct G φ η := by
    simp [Section1.scalarProduct, Finset.sum_neg_distrib]
  rw [hneg]
  ring

private theorem cfNormSq_eq_inv_card_mul_sum_normSq_pf72
    {G : Type*} [Group G] [Finite G]
    (φ : Section1.ClassFunction G) :
    Section5.cfNormSq φ = (Nat.card G : ℝ)⁻¹ * ∑ g : G, Complex.normSq (φ g) := by
  unfold Section5.cfNormSq Section1.scalarProduct
  have hcast : ((Nat.card G : ℂ)⁻¹) = (((Nat.card G : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp
  rw [hcast, Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro g _hg
  calc
    Complex.re (φ g * star (φ g)) = Complex.re (star (φ g) * φ g) := by
      rw [mul_comm]
    _ = Complex.re ((Complex.normSq (φ g) : ℝ) : ℂ) := by
          congr 1
          simpa using (Complex.normSq_eq_conj_mul_self (z := φ g)).symm
    _ = Complex.normSq (φ g) := by
          simp

private theorem cfNormSq_nonneg_pf72
    {G : Type*} [Group G] [Finite G]
    (φ : Section1.ClassFunction G) :
    0 ≤ Section5.cfNormSq φ := by
  rw [cfNormSq_eq_inv_card_mul_sum_normSq_pf72]
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun g _hg => Complex.normSq_nonneg (φ g)))

private theorem cfNormSq_eq_zero_pf72
    {G : Type*} [Group G] [Finite G]
    {φ : Section1.ClassFunction G}
    (hφ : Section5.cfNormSq φ = 0) :
    φ = 0 := by
  rw [cfNormSq_eq_inv_card_mul_sum_normSq_pf72] at hφ
  have hcardNat : 0 < Nat.card G := Nat.card_pos
  have hcardReal : 0 < (Nat.card G : ℝ) := by
    exact_mod_cast hcardNat
  have hcard : 0 < (Nat.card G : ℝ)⁻¹ := inv_pos.mpr hcardReal
  have hsumZero : (∑ g : G, Complex.normSq (φ g)) = 0 := by
    nlinarith
  have hzeroAll : ∀ g ∈ (Finset.univ : Finset G), Complex.normSq (φ g) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun g _hg => Complex.normSq_nonneg (φ g))).1 hsumZero
  ext g
  exact Complex.normSq_eq_zero.mp (hzeroAll g (by simp))

private theorem cfNormSq_add_eq_add_of_orthogonal_pf72
    {G : Type*} [Group G] [Finite G]
    {φ ψ : Section1.ClassFunction G}
    (hφψ : Section1.scalarProduct G φ ψ = 0)
    (hψφ : Section1.scalarProduct G ψ φ = 0) :
    Section5.cfNormSq (φ + ψ) = Section5.cfNormSq φ + Section5.cfNormSq ψ := by
  unfold Section5.cfNormSq
  rw [Section1.scalarProduct_add_left, scalarProduct_add_right_pf72,
    scalarProduct_add_right_pf72]
  simp [hφψ, hψφ]

private theorem dadeProjectionOn_CFon_pf72
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Section2.Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L)
    (χ : Section1.ClassFunction G) (hχclass : Section1.IsClassFunction χ) :
    Section2.CFOn L A (dadeProjectionOn A L H χ) := by
  constructor
  · intro x a
    have hxAiff : ((x * a * x⁻¹ : L) : G) ∈ A ↔ (a : G) ∈ A := by
      have hxAiff' := h.L_le_normalizer x.2 (a : G)
      change (↑x * ↑a * (↑x)⁻¹ : G) ∈ A ↔ (↑a : G) ∈ A at hxAiff'
      exact hxAiff'
    by_cases ha : (a : G) ∈ A
    · have hxa : ((x * a * x⁻¹ : L) : G) ∈ A := hxAiff.2 ha
      have hxa' : (↑x * ↑a * (↑x)⁻¹ : G) ∈ A := by
        simpa using hxa
      simp [dadeProjectionOn, hxa', ha, dadeProjection]
      exact Section2.dadeAveragingFunction_isClassFunction_on_A A L H h hAL χ hχclass a ha x
    · have hxa : ((x * a * x⁻¹ : L) : G) ∉ A := fun hmem => ha (hxAiff.1 hmem)
      have hxa' : (↑x * ↑a * (↑x)⁻¹ : G) ∉ A := by
        simpa using hxa
      simp [dadeProjectionOn, hxa', ha]
  · intro a ha
    simp [dadeProjectionOn, ha]

public theorem theorem_7_2_b
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G)
    (hAL : ∀ a ∈ A, a ∈ L) :
    theorem_7_2_b_statement A L H hAL := by
  intro h71 χ hχclass
  let ρ : Section1.ClassFunction L := dadeProjectionOn A L H χ
  let τρ : Section1.ClassFunction G := Section2.dadeTransform H hAL ρ
  let r : Section1.ClassFunction G := χ - τρ
  have hρ : Section2.CFOn L A ρ :=
    dadeProjectionOn_CFon_pf72 h71 hAL χ hχclass
  have hiso : Section1.scalarProduct G τρ τρ = Section1.scalarProduct L ρ ρ := by
    exact (Section2.theorem_2_6 A L H h71 hAL).1 ρ ρ hρ hρ
  have hagree : ∀ ⦃a : G⦄, (ha : a ∈ A) →
      ρ ⟨a, hAL a ha⟩ = Section2.dadeAveragingFunction L H χ ⟨a, hAL a ha⟩ := by
    intro a ha
    simp [ρ, dadeProjectionOn, dadeProjection, ha]
  have hinner : Section1.scalarProduct G τρ χ = Section1.scalarProduct L ρ ρ := by
    have h27 := Section2.proposition_2_7 A L H h71 hAL ρ χ hρ hχclass ρ hρ.1 hagree
    simpa [τρ] using h27.1
  have horth : Section1.scalarProduct G τρ r = 0 := by
    dsimp [r]
    rw [scalarProduct_sub_right_pf72, hinner, hiso, sub_self]
  have horth' : Section1.scalarProduct G r τρ = 0 := by
    rw [← Section1.scalarProduct_star_swap]
    simp [horth]
  have hτnorm : Section5.cfNormSq τρ = Section5.cfNormSq ρ := by
    unfold Section5.cfNormSq
    exact congrArg Complex.re hiso
  have hχ_decomp : χ = τρ + r := by
    ext g
    simp [r]
  have hnorm_decomp : Section5.cfNormSq χ = Section5.cfNormSq ρ + Section5.cfNormSq r := by
    rw [hχ_decomp, cfNormSq_add_eq_add_of_orthogonal_pf72 horth horth', hτnorm]
  constructor
  · rw [hnorm_decomp]
    exact le_add_of_nonneg_right (cfNormSq_nonneg_pf72 r)
  · constructor
    · intro heq
      have hrnorm : Section5.cfNormSq r = 0 := by
        nlinarith [cfNormSq_nonneg_pf72 r]
      have hrzero : r = 0 := cfNormSq_eq_zero_pf72 hrnorm
      refine ⟨ρ, hρ, ?_⟩
      dsimp [r] at hrzero
      ext g
      have hg := congrArg (fun f : Section1.ClassFunction G => f g) hrzero
      simpa [sub_eq_zero] using hg
    · rintro ⟨α, hα, hχ⟩
      have hρ_eq : ρ = α := by
        ext a
        by_cases ha : (a : G) ∈ A
        · simp [ρ, hχ, dadeProjectionOn, ha, theorem_7_2_a A L H hAL h71 α hα a ha]
        · simp [ρ, hχ, dadeProjectionOn, ha, hα.2 a ha]
      have hχnorm : Section5.cfNormSq χ = Section5.cfNormSq α := by
        rw [hχ]
        unfold Section5.cfNormSq
        exact congrArg Complex.re ((Section2.theorem_2_6 A L H h71 hAL).1 α α hα hα)
      change Section5.cfNormSq ρ = Section5.cfNormSq χ
      rw [hρ_eq, hχnorm]

end CFSG.Section7
