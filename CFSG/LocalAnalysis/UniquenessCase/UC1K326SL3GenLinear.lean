module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326SL3GenCore
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326SL3GenFrame
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326SL3GenField
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326SL3GenZeta
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectCentralAutomorphism

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

open Matrix

namespace SL3G

section Linear

variable {K : Type} [Field K] [Finite K]

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation toGL_slConjugation)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (slFieldAut)

private theorem toGL_slFieldAut (σ : K ≃+* K) (g : SpecialLinearGroup (Fin 3) K) :
    Matrix.SpecialLinearGroup.toGL (slFieldAut (Fin 3) K σ g) =
      GeneralLinearGroup.map (σ : K →+* K) (Matrix.SpecialLinearGroup.toGL g) := by
  apply Units.ext
  ext i j
  rfl

private theorem classify_linear (α : MulAut (SpecialLinearGroup (Fin 3) K)) (hα : α ^ 3 = 1) :
    ∃ (σ : K ≃+* K) (B : GL (Fin 3) K), (σ = 1 ∨ orderOf σ = 3) ∧
      ActsAs (Matrix.SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 3) K →* GL (Fin 3) K)
        α σ B := by
  have hlift : ∀ γ : MulAut (SpecialLinearGroup (Fin 3) K),
      descendAut 3 K γ = descendAut 3 K α → α = γ := by
    intro γ hγ
    apply CFSG.GorensteinWalter.perfect_central_automorphism_eq
      (CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl)
    intro g
    rw [← scalars_eq_center, ← ker_proj, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one,
      ← descendAut_proj, ← descendAut_proj, hγ]
  have hα3 : descendAut 3 K α ^ 3 = 1 := by rw [← map_pow, hα, map_one]
  by_cases hD : descendAut 3 K α ∈ linearAutGroup 3 K
  · rw [linearAutGroup_eq_range] at hD
    obtain ⟨A, hA⟩ := hD
    have hαA : α = slConjugation 3 K A := hlift _ hA
    refine ⟨1, A, Or.inl rfl, fun g => ?_⟩
    have hone : ∀ M : Matrix (Fin 3) (Fin 3) K, M.map ⇑(1 : K ≃+* K) = M := fun M => by
      ext i j
      rfl
    rw [hone, hαA, toGL_slConjugation, Units.val_mul, Units.val_mul]
  · obtain ⟨σ, hσ3, H, hαH⟩ :=
      CFSG.RankThree.PartTwo.KFacts.linear_order_three_field_descent le_rfl _ hα3 hD
    have hβ : α = slConjugation 3 K H * slFieldAut (Fin 3) K σ * (slConjugation 3 K H)⁻¹ :=
      hlift _ (by rw [hαH, map_mul, map_mul, map_inv]; rfl)
    have key : ∀ x : GL (Fin 3) K,
        H * GeneralLinearGroup.map (σ : K →+* K) (H⁻¹ * x * H) * H⁻¹ =
        (H * GeneralLinearGroup.map (σ : K →+* K) H⁻¹) *
          GeneralLinearGroup.map (σ : K →+* K) x *
          (H * GeneralLinearGroup.map (σ : K →+* K) H⁻¹)⁻¹ := by
      intro x
      rw [map_mul, map_mul, map_inv]
      group
    refine ⟨σ, H * GeneralLinearGroup.map (σ : K →+* K) H⁻¹, Or.inr hσ3, fun g => ?_⟩
    have h1 : Matrix.SpecialLinearGroup.toGL (α g) =
        (H * GeneralLinearGroup.map (σ : K →+* K) H⁻¹) *
          GeneralLinearGroup.map (σ : K →+* K) (Matrix.SpecialLinearGroup.toGL g) *
          (H * GeneralLinearGroup.map (σ : K →+* K) H⁻¹)⁻¹ := by
      rw [hβ, MulAut.mul_apply, MulAut.mul_apply, toGL_slConjugation, toGL_slFieldAut,
        ← map_inv, toGL_slConjugation, inv_inv, key]
    have h2 := congrArg Units.val h1
    rw [Units.val_mul, Units.val_mul] at h2
    exact h2

private theorem linear_conj : ConjProp
    (Matrix.SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 3) K →* GL (Fin 3) K) ⊤ := by
  intro θ _
  refine ⟨CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K θ⁻¹,
    fun g => ?_⟩
  change Matrix.SpecialLinearGroup.toGL
      (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K θ⁻¹ g) = _
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
  simp

private theorem linear_frame (h3 : 3 ∣ Nat.card K - 1) : FrameProp
    (Matrix.SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 3) K →* GL (Fin 3) K) ⊤ := by
  intro T Q u hQab hQn hu huR hu3 hnsc
  obtain ⟨ω, hω⟩ := exists_primitiveRoot_three h3
  obtain ⟨g, rfl⟩ := huR
  obtain ⟨θ, ε, hfr⟩ := frame_exists hω T Q hQab hQn hu hu3 g.2 hnsc
  exact ⟨θ, Subgroup.mem_top θ, ε, hfr⟩

private theorem linear_block : BlockProp
    (Matrix.SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 3) K →* GL (Fin 3) K) := by
  intro H hH
  rw [eq_top_iff, ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (ι := Fin 3) (K := K), Subgroup.closure_le]
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
  exact hH i j hij _ (isCoordBlockOn_transvection hij c)

private theorem linear_field (h3 : 3 ∣ Nat.card K - 1) : FieldProp
    (Matrix.SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 3) K →* GL (Fin 3) K) := by
  intro α T σ B hH hσ hα hmono hdiag
  obtain ⟨ζ, hζ, h1, h2, h3'⟩ := exists_zeta_linear h3 hσ
  refine field_false Matrix.SpecialLinearGroup.toGL_injective hH hα hmono hdiag hζ ?_ h1 h2 h3'
  refine ⟨⟨diagonal ![(ζ : K), ((ζ⁻¹ : Kˣ) : K), 1], ?_⟩, rfl⟩
  simp [det_diagonal, Fin.prod_univ_three]

theorem linearModelGen (h3 : 3 ∣ Nat.card K - 1) : ModelGen (SpecialLinearGroup (Fin 3) K) :=
  model_generic Matrix.SpecialLinearGroup.toGL_injective linear_conj (linear_frame h3)
    classify_linear linear_block (linear_field h3)

end Linear

end SL3G

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
