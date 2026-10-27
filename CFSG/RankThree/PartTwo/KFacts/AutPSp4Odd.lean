module

public import CFSG.RankThree.PartTwo.KFacts.AutPSpOrderThree
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoGeneration
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoTypePreservation

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

theorem stdPinnedPSp_stable_of_forall {r : ℕ} {K : Type} [Field K] [Finite K]
    (hform : ∀ α : MulAut (StatedProj (StatedSp r K)), ∃ (A : gsp r K) (σ : K ≃+* K),
      α = conjAut r K A * fieldAut r K σ) :
    (stdPinnedPSp r K).Stable := by
  have hcomm : ∀ σ τ : K ≃+* K, fieldAut r K σ * fieldAut r K τ = fieldAut r K τ * fieldAut r K σ :=
    fun σ τ => by
      rw [← map_mul, ← map_mul, CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K σ τ]
  have hconj : ∀ α : MulAut (StatedProj (StatedSp r K)), ∃ A : gsp r K, ∀ τ : K ≃+* K,
      α * fieldAut r K τ * α⁻¹ = conjAut r K A * fieldAut r K τ * (conjAut r K A)⁻¹ := by
    intro α
    obtain ⟨A, σ, rfl⟩ := hform α
    refine ⟨A, fun τ => ?_⟩
    have h1 := hcomm σ τ
    calc conjAut r K A * fieldAut r K σ * fieldAut r K τ * (conjAut r K A * fieldAut r K σ)⁻¹ =
        conjAut r K A * (fieldAut r K σ * fieldAut r K τ) * (fieldAut r K σ)⁻¹ *
          (conjAut r K A)⁻¹ := by group
      _ = conjAut r K A * fieldAut r K τ * (conjAut r K A)⁻¹ := by rw [h1]; group
  refine ⟨⟨fun d hd α => ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨B, rfl⟩ := hd
    obtain ⟨A, σ, rfl⟩ := hform α
    refine ⟨A * gspFieldMap σ B * A⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv, ← fieldAut_mul_conjAut_mul_inv]
    group
  · rintro α _ ⟨τ, rfl⟩ h1
    obtain ⟨A, hA⟩ := hconj α
    exact ⟨fieldAut r K τ, ⟨τ, rfl⟩, h1, conjAut r K A, ⟨A, rfl⟩, hA τ⟩
  · rintro α γ hγ
    exact absurd hγ (Set.notMem_empty γ)
  · rintro α γ φ hγ
    exact absurd hγ (Set.notMem_empty γ)

variable {K : Type} [Field K] [Finite K]

theorem psp4_odd_automorphism_normal_form (hodd : ringChar K ≠ 2)
    (α : MulAut (StatedProj (StatedSp 2 K))) :
    ∃ (A : gsp 2 K) (σ : K ≃+* K), α = conjAut 2 K A * fieldAut 2 K σ := by
  obtain ⟨-, hform, -, -⟩ :=
    CFSG.ComponentClassification.CatalogueBSymplecticTwo.kernel_generation (K := K)
  obtain ⟨-, htop, -⟩ :=
    CFSG.ComponentClassification.CatalogueBSymplecticTwo.odd_symplectic_two_type_preservation
      hodd
  exact hform α (htop ▸ Subgroup.mem_top α)

theorem stdPinnedPSp_two_stable (hodd : ringChar K ≠ 2) : (stdPinnedPSp 2 K).Stable :=
  stdPinnedPSp_stable_of_forall (psp4_odd_automorphism_normal_form hodd)

theorem psp4_odd_order_three_field_descent (hodd : ringChar K ≠ 2)
    (α : MulAut (StatedProj (StatedSp 2 K))) (hα : α ^ 3 = 1)
    (hD : α ∉ (conjAut 2 K).range) :
    ∃ σ : K ≃+* K, orderOf σ = 3 ∧ ∃ H : gsp 2 K,
      α = conjAut 2 K H * fieldAut 2 K σ * (conjAut 2 K H)⁻¹ := by
  obtain ⟨A, σ, rfl⟩ := psp4_odd_automorphism_normal_form hodd α
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [map_one, mul_one] at hD
    exact hD ⟨A, rfl⟩
  obtain ⟨h3, H, hH⟩ := conjAut_mul_fieldAut_of_pow_three_eq_one (by norm_num) A σ hσ1 hα
  exact ⟨σ, h3, H, hH⟩

theorem isField_psp_two_of_pow_three_eq_one (hodd : ringChar K ≠ 2)
    {α : MulAut (StatedProj (StatedSp 2 K))} (hα : α ^ 3 = 1)
    (hD : α ∉ (conjAut 2 K).range) : (stdPinnedPSp 2 K).IsField α := by
  obtain ⟨σ, hσ, H, rfl⟩ := psp4_odd_order_three_field_descent hodd α hα hD
  refine ⟨fieldAut 2 K σ, ⟨σ, rfl⟩, fun h1 => ?_, conjAut 2 K H, ⟨H, rfl⟩, rfl⟩
  have h2 := (fieldAut_mem_range_conjAut_iff (r := 2) (K := K) (by norm_num)).mp
    (by rw [h1]; exact one_mem _)
  rw [h2, orderOf_one] at hσ
  omega

section Induced

variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)

theorem inducesKindPSp_two_iff (hodd : ringChar K ≠ 2)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* StatedProj (StatedSp 2 K)) (x : G) (k : AutKind) :
    InducesKindPSp 2 K L x k ↔ InducesKind L (stdPinnedPSp 2 K) e x k :=
  inducesKindPSp_iff_of_stable L (stdPinnedPSp_two_stable hodd) e x k

theorem inducesKindPSp_two_unique (hodd : ringChar K ≠ 2) {x : G} {k₁ k₂ : AutKind}
    (h₁ : InducesKindPSp 2 K L x k₁) (h₂ : InducesKindPSp 2 K L x k₂) : k₁ = k₂ := by
  obtain ⟨e, h₁⟩ := h₁
  exact InducesKind.unique L (stdPinnedPSp_separated (by norm_num)) h₁
    ((inducesKindPSp_two_iff L hodd e x k₂).mp h₂)

theorem inducesKindPSp_two_diagonal_or_field (hodd : ringChar K ≠ 2) {x : G} (hx3 : x ^ 3 = 1)
    (hout : InducesOuterTheta x L)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* StatedProj (StatedSp 2 K)) :
    InducesKind L (stdPinnedPSp 2 K) e x .diagonal ∨
      InducesKind L (stdPinnedPSp 2 K) e x .field := by
  obtain ⟨hx, -⟩ := id hout
  have hnot := (not_isInnerAut_inducedAutHom_iff L e hx).mpr hout
  by_cases hD : inducedAutHom L e ⟨x, hx⟩ ∈ (conjAut 2 K).range
  · exact Or.inl ⟨hx, hD, hnot⟩
  · exact Or.inr ⟨hx, isField_psp_two_of_pow_three_eq_one hodd
      (inducedAutHom_pow_eq_one L e hx hx3) hD⟩

end Induced

end CFSG.RankThree.PartTwo.KFacts
