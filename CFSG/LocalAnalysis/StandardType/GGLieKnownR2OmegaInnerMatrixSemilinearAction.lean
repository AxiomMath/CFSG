module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaInnerDefs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaInnerRootTransport
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaInnerTriality
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaInnerAutomorphismCalc
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityModel

public section

open CFSG.Open CFSG.StandardType CFSG.StandardType.Triality CFSG.LieType.Universal
  CFSG.LieType.RootSystem
open Matrix TauCeti
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.AUTSL

namespace CFSG.StandardType.LieKnownR2.POmega.Inner

private theorem itrans_reindex_symm_glFieldAut {F : Type} [Field F]
    (e : Fin 4 ⊕ Fin 4 ≃ Fin (2 * 4)) (σ : F ≃+* F) (M : GL (Fin 4 ⊕ Fin 4) F) :
    (reindexMatrixEquiv e).symm
        (glFieldAut (Fin (2 * 4)) F σ (reindexMatrixEquiv e M)) =
      glFieldEquiv (Fin 4 ⊕ Fin 4) σ M := by
  apply Units.ext
  ext i j
  rw [reindexMatrixEquiv_symm_val]
  change σ (M.val (e.symm (e i)) (e.symm (e j))) = σ (M.val i j)
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem exists_semilinear_similitude_of_conjAct {F : Type} [Field F] [CharP F 2]
    {y : MulAut ↥(spinGroup (Spin.quadPlus 4 F))}
    {g : similarityPairs (coordinateQuadPlus 4 F)}
    (hconj : MulAut.congr (trialityIsomorphism (F := F)) y = conjAct (coordinateQuadPlus 4 F) g) :
    ∃ (A : GL (Fin 4 ⊕ Fin 4) F) (φ : F ≃+* F) (μ : Fˣ),
      GGSemilinearSimilitude (Spin.quadPlus 4 F) A φ μ ∧
        GGMatrixSemilinearAction (Spin.quadPlus 4 F) A φ μ y := by
  obtain ⟨μ, hμ⟩ := g.2
  set e : Fin 4 ⊕ Fin 4 ≃ Fin (2 * 4) := plusIndexEquiv 4
  refine ⟨(reindexMatrixEquiv e).symm g.val.left, g.val.right, μ, ?_, ?_⟩
  · intro v
    have key : reindexVectorEquiv e (((reindexMatrixEquiv e).symm g.val.left).val *ᵥ
        (fun i => g.val.right (v i))) =
        coordinateSemilinearMap g.val (reindexVectorEquiv e v) := by
      rw [← reindexMatrixEquiv_mulVec, MulEquiv.apply_symm_apply, coordinateSemilinearMap_apply,
        matrixLinearEquiv_apply]
      rfl
    have h1 := reindexQuadraticForm_map e (Spin.quadPlus 4 F)
      (((reindexMatrixEquiv e).symm g.val.left).val *ᵥ (fun i => g.val.right (v i)))
    rw [← h1, key]
    have h2 := hμ (reindexVectorEquiv e v)
    rw [show reindexQuadraticForm e (Spin.quadPlus 4 F) = coordinateQuadPlus 4 F from rfl, h2]
    congr 2
    exact reindexQuadraticForm_map e (Spin.quadPlus 4 F) v
  · intro x
    have hα : ((conjAct (coordinateQuadPlus 4 F) g (model8 x) : Om8 F) :
          GL (Fin (2 * 4)) F) =
        ((MulAut.congr modelEquiv8 y (model8 x) : Om8 F) : GL (Fin (2 * 4)) F) := by
      have h := congrArg (fun f : MulAut (Om8 F) =>
        ((f (model8 x) : Om8 F) : GL (Fin (2 * 4)) F)) hconj.symm
      exact h
    rw [← modelEquiv8_apply, congr_apply_apply', modelEquiv8_apply, conjAct_apply,
      matrixDerivedConjugation_val] at hα
    have hval : ∀ z : Sp8 F, ((model8 z : Om8 F) : GL (Fin (2 * 4)) F) =
        reindexMatrixEquiv e (Spin.spinMatrix (Spin.quadPlus 4 F) z) := fun z => rfl
    rw [hval, modelEquiv8_apply, hval] at hα
    have h3 := congrArg (reindexMatrixEquiv e).symm hα
    rw [MulEquiv.symm_apply_apply, map_mul, map_mul, map_inv,
      itrans_reindex_symm_glFieldAut] at h3
    exact h3.symm

theorem congr_triSpinAut_conj {F : Type} [Field F] [Finite F] [CharP F 2]
    (y : MulAut ↥(spinGroup (Spin.quadPlus 4 F))) (j : ℕ) :
    MulAut.congr (trialityIsomorphism (F := F))
        ((triSpinAut : MulAut ↥(spinGroup (Spin.quadPlus 4 F))) ^ j * y *
          ((triSpinAut : MulAut ↥(spinGroup (Spin.quadPlus 4 F))) ^ j)⁻¹) =
      (theta : MulAut (Om8 F)) ^ j * MulAut.congr (trialityIsomorphism (F := F)) y *
        ((theta : MulAut (Om8 F)) ^ j)⁻¹ := by
  rw [map_mul, map_mul, map_inv]
  have h : (MulAut.congr (trialityIsomorphism (F := F)))
      (triSpinAut ^ j : MulAut ↥(spinGroup (Spin.quadPlus 4 F))) =
      (theta : MulAut (Om8 F)) ^ j := by
    rw [map_pow, trialityIsomorphism_triSpinAut]
  rw [h]


theorem exists_semilinear_similitude_of_triality_conj {F : Type} [Field F] [Finite F] [CharP F 2]
    (y : MulAut ↥(spinGroup (Spin.quadPlus 4 F))) (m : ℕ) (hy2 : y ^ 2 ^ m = 1) :
    ∃ j : ℕ, ∃ (A : GL (Fin 4 ⊕ Fin 4) F) (φ : F ≃+* F) (μ : Fˣ),
      GGSemilinearSimilitude (Spin.quadPlus 4 F) A φ μ ∧
        GGMatrixSemilinearAction (Spin.quadPlus 4 F) A φ μ
          ((triSpinAut : MulAut ↥(spinGroup (Spin.quadPlus 4 F))) ^ j * y *
            ((triSpinAut : MulAut ↥(spinGroup (Spin.quadPlus 4 F))) ^ j)⁻¹) := by
  let α : MulAut (Om8 F) := MulAut.congr (trialityIsomorphism (F := F)) y
  have hα : α ^ 2 ^ m = 1 := by
    change (MulAut.congr (trialityIsomorphism (F := F)) y) ^ 2 ^ m = 1
    rw [← map_pow, hy2, map_one]
  obtain ⟨j, g, hg⟩ := exists_theta_pow_conj_eq_conjAct α m hα
  refine ⟨j, ?_⟩
  have hconj : MulAut.congr (trialityIsomorphism (F := F))
      ((triSpinAut : MulAut ↥(spinGroup (Spin.quadPlus 4 F))) ^ j * y *
        ((triSpinAut : MulAut ↥(spinGroup (Spin.quadPlus 4 F))) ^ j)⁻¹) =
      conjAct (coordinateQuadPlus 4 F) g := by
    rw [congr_triSpinAut_conj]
    exact hg
  obtain ⟨A, φ, μ, hsim, hmat⟩ := exists_semilinear_similitude_of_conjAct hconj
  exact ⟨A, φ, μ, hsim, hmat⟩

end CFSG.StandardType.LieKnownR2.POmega.Inner
