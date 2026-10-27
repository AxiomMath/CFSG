module

public import CFSG.LinearAlgebra.FixedPointFreeOrderThreeField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearCoordinates

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LinearAlgebra CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear Subgroup

theorem s16h_e3_z3_det_eq_one_of_sq {g : Matrix.GeneralLinearGroup (Fin 3) OmegaField}
    (hg : g ^ 2 = 1) : (g : Matrix (Fin 3) (Fin 3) OmegaField).det = 1 := by
  have hmat : (g : Matrix (Fin 3) (Fin 3) OmegaField) ^ 2 = 1 := by
    simpa using
      congrArg (fun u : (Matrix (Fin 3) (Fin 3) OmegaField)ˣ =>
        (u : Matrix (Fin 3) (Fin 3) OmegaField)) hg
  have hdet : (g : Matrix (Fin 3) (Fin 3) OmegaField).det ^ 2 = 1 := by
    simpa [Matrix.det_pow] using congrArg Matrix.det hmat
  have hneg : (-1 : OmegaField) = 1 := by
    refine neg_eq_iff_add_eq_zero.mpr ?_
    rw [one_add_one_eq_two]
    exact omegaField_two_eq_zero
  rcases sq_eq_one_iff.mp hdet with h | h
  · exact h
  · rw [h, hneg]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
