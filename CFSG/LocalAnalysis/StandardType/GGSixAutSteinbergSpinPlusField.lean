module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaPlusOTwo
public import CFSG.LieType.Steinberg.Classical.SpinPlus.Basic

public noncomputable section

namespace CFSG.StandardType

open CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg CFSG.LieType.Steinberg.SpinFrame
  CFSG.LieType.RootSystem CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBHigherLinearField CFSG.RankThree.PartOne.AUTSL

variable {K : Type} [Field K] [CharP K 2] {n : ℕ}

namespace OrdPGraphOmega

omit [CharP K 2] in
theorem fieldAutP_spinModelPlus_longRoot (hn : 3 ≤ n) (σ : K ≃+* K) {i j : Fin n} (hij : i ≠ j)
    (s t : Bool) (c : K) :
    AutOm.fieldAutP n σ (AutOm.spinModelPlus hn ((plusFrame n K hn).longRoot hij s t (.ofAdd c))) =
      AutOm.spinModelPlus hn ((plusFrame n K hn).longRoot hij s t (.ofAdd (σ c))) := by
  rw [AutOm.fieldAutP_eq]
  refine AutOm.conjAct_eichler_eq (AutOm.gField σ) (AutOm.gField_form σ) _ _
    (AutOm.spinModelPlus_longRoot_eichler hn hij s t c)
    (AutOm.spinModelPlus_longRoot_eichler hn hij s t (σ c)) ?_ ?_
  · rw [AutOm.coordinateSemilinearMap_fieldPair, AutOm.coordinateFieldMap_pvec]
  · rw [coordinateSemilinearMap_smul, AutOm.coordinateSemilinearMap_fieldPair,
      AutOm.coordinateFieldMap_pvec]
    rfl

end OrdPGraphOmega

namespace AutOm

@[expose] def spinModelPlusEquiv (hn : 3 ≤ n) :
    spinGroup (quadPlus n K) ≃* matrixDerived (coordinateQuadPlus n K) :=
  MulEquiv.ofBijective (spinModelPlus (K := K) hn)
    ⟨spinModelPlus_injective hn, spinModelPlus_surjective hn⟩

@[expose] def spinFieldAutP (hn : 3 ≤ n) : (K ≃+* K) →* MulAut (spinGroup (quadPlus n K)) :=
  (MulAut.congr (spinModelPlusEquiv hn).symm).toMonoidHom.comp (fieldAutP n)

theorem spinModelPlus_spinFieldAutP (hn : 3 ≤ n) (σ : K ≃+* K) (s : spinGroup (quadPlus n K)) :
    spinModelPlus hn (spinFieldAutP hn σ s) =
      fieldAutP n σ (spinModelPlus hn s) := by
  unfold spinFieldAutP
  change spinModelPlusEquiv hn ((spinModelPlusEquiv hn).symm
    (fieldAutP n σ (spinModelPlusEquiv hn s))) = _
  exact (spinModelPlusEquiv hn).apply_symm_apply _

theorem spinFieldAutP_longRoot (hn : 3 ≤ n) (σ : K ≃+* K) {i j : Fin n}
    (hij : i ≠ j) (b c : Bool) (t : K) :
    spinFieldAutP hn σ ((plusFrame n K hn).longRoot hij b c (.ofAdd t)) =
      (plusFrame n K hn).longRoot hij b c (.ofAdd (σ t)) := by
  apply spinModelPlus_injective hn
  rw [spinModelPlus_spinFieldAutP, OrdPGraphOmega.fieldAutP_spinModelPlus_longRoot]


theorem spinFieldAutP_x (hn : 3 ≤ n) (σ : K ≃+* K) {γ : Fin n → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanD n) ∅) (c : K) :
    spinFieldAutP hn σ (SpinPlus.x n K hn γ c) = SpinPlus.x n K hn γ (σ c) := by
  obtain ⟨i, j, hij, b, t, he⟩ := (SpinPlus.isLong_toStdD_iff (by omega)).mpr hγ
  unfold SpinPlus.x
  rw [rootElt_eq (plusFrame n K hn) hij he, rootElt_eq (plusFrame n K hn) hij he]
  rw [spinFieldAutP_longRoot]
  congr 1
  simp only [map_mul, map_intCast]

theorem spinAction_spinFieldAutP (hn : 3 ≤ n) (σ : K ≃+* K)
    (s : spinGroup (quadPlus n K)) (v : Fin n ⊕ Fin n → K) :
    spinAction (quadPlus n K) (spinFieldAutP hn σ s) (fun i => σ (v i)) =
      fun i => σ (spinAction (quadPlus n K) s v i) := by
  have hreindex (w : Fin n ⊕ Fin n → K) :
      reindexVectorEquiv (plusIndexEquiv n) (fun i => σ (w i)) =
        coordinateFieldMap (2 * n) σ (reindexVectorEquiv (plusIndexEquiv n) w) := by
    ext i
    simp only [reindexVectorEquiv_apply, coordinateFieldMap_apply]
  have hval : ((fieldAutP n σ (spinModelPlus hn s) :
      matrixDerived (coordinateQuadPlus n K)) : GL (Fin (2 * n)) K) =
        glFieldAut (Fin (2 * n)) K σ (spinModelPlus hn s : GL (Fin (2 * n)) K) := by
    exact CFSG.RankThree.PartOne.KCOrthogonalSubfield.matrixDerivedConjugation_fieldPair_val
      (coordinateQuadPlus n K) σ (CFSG.SeitzReduction.E7Pilot.coordinateQuadPlus_fieldMap n σ) _
  have hM := coordinateFieldMap_matrix σ
    (spinModelPlus hn s : GL (Fin (2 * n)) K) (reindexVectorEquiv (plusIndexEquiv n) v)
  rw [matrixLinearEquiv_apply, matrixLinearEquiv_apply] at hM
  apply (reindexVectorEquiv (K := K) (plusIndexEquiv n)).injective
  calc
    _ = Matrix.mulVec ((spinModelPlus hn (spinFieldAutP hn σ s) :
        GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K)
        (reindexVectorEquiv (plusIndexEquiv n) (fun i => σ (v i))) :=
      (spinModelPlus_mulVec hn _ _).symm
    _ = Matrix.mulVec ((glFieldAut (Fin (2 * n)) K σ
        (spinModelPlus hn s : GL (Fin (2 * n)) K)) :
        Matrix (Fin (2 * n)) (Fin (2 * n)) K)
        (coordinateFieldMap (2 * n) σ (reindexVectorEquiv (plusIndexEquiv n) v)) := by
      rw [spinModelPlus_spinFieldAutP, hval, hreindex]
    _ = coordinateFieldMap (2 * n) σ
        (Matrix.mulVec ((spinModelPlus hn s : GL (Fin (2 * n)) K) :
          Matrix (Fin (2 * n)) (Fin (2 * n)) K) (reindexVectorEquiv (plusIndexEquiv n) v)) := hM.symm
    _ = _ := by rw [spinModelPlus_mulVec, ← hreindex]


end AutOm

end CFSG.StandardType
