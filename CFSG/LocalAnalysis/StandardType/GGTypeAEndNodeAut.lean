module

public import CFSG.LocalAnalysis.StandardType.GGTypeAEndNodeBlock
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt

public section

namespace CFSG.StandardType

open Matrix CFSG.ComponentClassification

variable {n : ℕ} {F : Type} [Field F]

variable (n F) in
@[expose] noncomputable def glUpperBlockHom : GL (Fin n) F →* GL (Fin (n + 1)) F :=
  Units.map (slUpperBlockMonoidHom n F)

theorem coe_glUpperBlockHom (A : GL (Fin n) F) :
    ((glUpperBlockHom n F A : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) =
      slUpperBlockMat n F (A : Matrix (Fin n) (Fin n) F) := rfl

theorem coe_glUpperBlockHom_inv (A : GL (Fin n) F) :
    (((glUpperBlockHom n F A)⁻¹ : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) =
      slUpperBlockMat n F ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := rfl

theorem slConjugation_slUpperBlockHom (A : GL (Fin n) F)
    (g : Matrix.SpecialLinearGroup (Fin n) F) :
    CatalogueBHigherLinearAction.slConjugation (n + 1) F (glUpperBlockHom n F A)
        (slUpperBlockHom n F g) =
      slUpperBlockHom n F (CatalogueBHigherLinearAction.slConjugation n F A g) := by
  apply Subtype.ext
  rw [CatalogueBHigherLinearAction.slConjugation_matrix, coe_slUpperBlockHom, coe_slUpperBlockHom,
    CatalogueBHigherLinearAction.slConjugation_matrix, slUpperBlockMat_mul, slUpperBlockMat_mul]
  rfl

theorem slFieldAut_slUpperBlockHom (σ : F ≃+* F) (g : Matrix.SpecialLinearGroup (Fin n) F) :
    CatalogueBHigherLinearField.slFieldAut (Fin (n + 1)) F σ (slUpperBlockHom n F g) =
      slUpperBlockHom n F (CatalogueBHigherLinearField.slFieldAut (Fin n) F σ g) := by
  apply Subtype.ext
  change (slUpperBlockMat n F (g : Matrix (Fin n) (Fin n) F)).map σ =
    slUpperBlockMat n F ((g : Matrix (Fin n) (Fin n) F).map σ)
  exact slUpperBlockMat_map (map_zero σ) (map_one σ) _

theorem slGraphAut_slUpperBlockHom (g : Matrix.SpecialLinearGroup (Fin n) F) :
    CatalogueBGraphForm.slGraphAut (n + 1) F (slUpperBlockHom n F g) =
      slUpperBlockHom n F (CatalogueBGraphForm.slGraphAut n F g) := by
  apply Subtype.ext
  rw [CatalogueBGraphForm.slGraphAut_matrix, ← map_inv, coe_slUpperBlockHom,
    slUpperBlockMat_transpose, coe_slUpperBlockHom, CatalogueBGraphForm.slGraphAut_matrix]

theorem exists_mulAut_slUpperBlockHom [Finite F] (hn : 3 ≤ n)
    (β : MulAut (Matrix.SpecialLinearGroup (Fin n) F)) :
    ∃ β' : MulAut (Matrix.SpecialLinearGroup (Fin (n + 1)) F),
      ∀ g, β' (slUpperBlockHom n F g) = slUpperBlockHom n F (β g) := by
  obtain ⟨A, σ, ε, hε, rfl⟩ := CFSG.RankThree.PartOne.AUTSL.exists_eq_std_of_mulAut_sl hn β
  refine ⟨CatalogueBHigherLinearAction.slConjugation (n + 1) F (glUpperBlockHom n F A) *
    CatalogueBHigherLinearField.slFieldAut (Fin (n + 1)) F σ *
      CatalogueBGraphForm.slGraphAut (n + 1) F ^ ε, fun g => ?_⟩
  have hγ : (CatalogueBGraphForm.slGraphAut (n + 1) F ^ ε) (slUpperBlockHom n F g) =
      slUpperBlockHom n F ((CatalogueBGraphForm.slGraphAut n F ^ ε) g) := by
    interval_cases ε
    · rfl
    · simp only [pow_one]
      exact slGraphAut_slUpperBlockHom g
  simp only [MulAut.mul_apply]
  rw [hγ, slFieldAut_slUpperBlockHom, slConjugation_slUpperBlockHom]

end CFSG.StandardType
