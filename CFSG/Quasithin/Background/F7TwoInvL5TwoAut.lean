module

public import CFSG.Quasithin.Background.F7TwoInvL5TwoGraph
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearPureGraph
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.Quasithin.F7Two

open CFSG.GroupTheory.GL52 CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] noncomputable def psiL5 : G52 ≃* projectiveSL 5 (ZMod 2) :=
  G52EquivPSL.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL 5 (ZMod 2))

theorem psiL5_toGL (s : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
    psiL5 (Matrix.SpecialLinearGroup.toGL s) = proj 5 (ZMod 2) s := by
  have h1 : (MulEquiv.ofBijective _ bijective_toGL_G52).symm
      (Matrix.SpecialLinearGroup.toGL s) = s := by
    rw [MulEquiv.symm_apply_eq]; rfl
  simp only [psiL5, G52EquivPSL, MulEquiv.trans_apply, h1]
  rfl

theorem conjAut_psiL5 (A g : G52) :
    conjAut 5 (ZMod 2) A (psiL5 g) = psiL5 (A * g * A⁻¹) := by
  obtain ⟨s, rfl⟩ := bijective_toGL_G52.2 g
  rw [psiL5_toGL, conjAut_proj]
  have : A * Matrix.SpecialLinearGroup.toGL s * A⁻¹ = Matrix.SpecialLinearGroup.toGL
      (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 5 (ZMod 2) A s) :=
    Units.ext (by simp only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      coe_slConjugation])
  rw [this, psiL5_toGL]

theorem dualAut_psiL5 (g : G52) : dualAut 5 (ZMod 2) (psiL5 g) = psiL5 (dualG g) := by
  obtain ⟨s, rfl⟩ := bijective_toGL_G52.2 g
  rw [psiL5_toGL, dualAut_proj]
  have : dualG (Matrix.SpecialLinearGroup.toGL s) =
      Matrix.SpecialLinearGroup.toGL ((s⁻¹).transpose) :=
    Units.ext (by
      rw [coe_dualG, ← map_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
        Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.coe_transpose])
  rw [this, psiL5_toGL]

noncomputable abbrev phiL5 : MulAut G52 ≃* MulAut (projectiveSL 5 (ZMod 2)) := MulAut.congr psiL5

theorem phiL5_conj (A : G52) : phiL5 (MulAut.conj A) = conjAut 5 (ZMod 2) A := by
  refine MulEquiv.ext fun q => ?_
  obtain ⟨g, rfl⟩ := psiL5.surjective q
  rw [conjAut_psiL5]
  simp [phiL5, MulAut.congr_apply, MulAut.conj_apply]

theorem phiL5_dualG : phiL5 dualG = dualAut 5 (ZMod 2) := by
  refine MulEquiv.ext fun q => ?_
  obtain ⟨g, rfl⟩ := psiL5.surjective q
  rw [dualAut_psiL5]
  simp [phiL5, MulAut.congr_apply]

theorem aut_involution_L5 (φ : MulAut G52) (hφ2 : φ * φ = 1) :
    (∃ A : G52, φ = MulAut.conj A) ∨
      ∃ H : G52, φ = MulAut.conj H * dualG * (MulAut.conj H)⁻¹ := by
  obtain ⟨A, σ, ε, hε, hψ⟩ :=
    (automorphism_generation (K := ZMod 2) (n := 5) (by norm_num)).2 (phiL5 φ)
  have hσ : σ = 1 := by
    ext x
    have hx : x = 0 ∨ x = 1 := by revert x; decide
    rcases hx with rfl | rfl <;> simp
  subst hσ
  rw [map_one, mul_one] at hψ
  interval_cases ε
  · left
    refine ⟨A, phiL5.injective ?_⟩
    rw [phiL5_conj]
    simpa using hψ
  · right
    have h2 : (conjAut 5 (ZMod 2) A * dualAut 5 (ZMod 2)) ^ 2 = 1 := by
      have := congrArg phiL5 hφ2
      rw [map_mul, map_one, hψ, pow_one] at this
      rwa [pow_two]
    obtain ⟨-, ⟨H, C, -, hHC, hC⟩, -⟩ :=
      UnitaryHigher.even_linear_pure_graph_involution_normal_forms (K := ZMod 2) (n := 5)
        (f := 1) le_rfl (by simp) (by norm_num) A h2
    rcases hC with ⟨hC1, -⟩ | ⟨r, hr, -⟩
    · have hC : C = 1 := Units.ext (by simpa using hC1)
      subst hC
      refine ⟨H, phiL5.injective ?_⟩
      rw [map_mul, map_mul, map_inv, phiL5_conj, phiL5_dualG, hψ, pow_one, hHC, map_one,
        one_mul]
    · omega

end CFSG.Quasithin.F7Two
