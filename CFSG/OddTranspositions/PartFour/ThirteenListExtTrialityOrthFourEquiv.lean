module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityModel

public section

namespace CFSG.OddTranspositions.PartFour.ExtTrialityOrthFour

open CFSG.StandardType.Triality CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

open CFSG.ClassicalGroups.Orthogonal (toLinEquiv closure_isometries_eq_comap)
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus)

@[expose] noncomputable def orthEquiv (F : Type) [Field F] :
    ↥(CFSG.PGLModel.orthogonalPlus 4 F) ≃* ↥(matrixIsometries (coordinateQuadPlus 4 F)) :=
  (((toLinEquiv (Fin 4 ⊕ Fin 4) F).subgroupMap (CFSG.PGLModel.orthogonalPlus 4 F)).trans
    (MulEquiv.subgroupCongr (by
      rw [show CFSG.PGLModel.orthogonalPlus 4 F =
          (TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 F)).comap
            (toLinEquiv (Fin 4 ⊕ Fin 4) F).toMonoidHom from
        closure_isometries_eq_comap (coe_quadPlus 4 F)]
      exact Subgroup.map_comap_eq_self_of_surjective (toLinEquiv _ F).surjective _))).trans
    ((TauCeti.QuadraticMap.orthogonalGroupCongr (coordinatePlusIsometry 4 F)).trans
      ((matrixLinearIso.subgroupMap (matrixIsometries (coordinateQuadPlus 4 F))).trans
        (MulEquiv.subgroupCongr
          (Subgroup.map_comap_eq_self_of_surjective matrixLinearIso.surjective _))).symm)

theorem map_derivedSeries_isometries (F : Type) [Field F] :
    (derivedSeries ↥(matrixIsometries (coordinateQuadPlus 4 F)) 1).map
        (matrixIsometries (coordinateQuadPlus 4 F)).subtype =
      matrixDerived (coordinateQuadPlus 4 F) := by
  rw [derivedSeries_one, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]
  rfl

@[expose] noncomputable def derivedOm8Equiv (F : Type) [Field F] :
    ↥(derivedSeries ↥(matrixIsometries (coordinateQuadPlus 4 F)) 1) ≃* Om8 F :=
  ((derivedSeries ↥(matrixIsometries (coordinateQuadPlus 4 F)) 1).equivMapOfInjective
    (matrixIsometries (coordinateQuadPlus 4 F)).subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr (map_derivedSeries_isometries F))

end CFSG.OddTranspositions.PartFour.ExtTrialityOrthFour
