module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearCoordinates
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts3A
public import CFSG.Quasithin.Vol2.Ch11SecS12ZD

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LinearAlgebra CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear Subgroup

theorem s16h_e3_z3_no_order_nine {g : Matrix.GeneralLinearGroup (Fin 3) OmegaField}
    (hdet : (g : Matrix (Fin 3) (Fin 3) OmegaField).det = 1) : orderOf g ≠ 9 := by
  intro hord
  haveI : Module.Finite (ZMod 2) OmegaField := (AdjoinRoot.powerBasis' omegaPoly_monic).finite
  haveI : Finite OmegaField := Module.finite_of_finite (ZMod 2)
  haveI : Fintype OmegaField := Fintype.ofFinite OmegaField
  have hF : Fintype.card OmegaField = 4 := by
    rw [← Nat.card_eq_fintype_card, s16h_e3_z3_card_omegaField_eq_four]
  have hg9 : g ^ 9 = 1 := by rw [← hord]; exact pow_orderOf_eq_one g
  have hmat9 : (g : Matrix (Fin 3) (Fin 3) OmegaField) ^ 9 = 1 := by
    simpa using
      congrArg (fun u : (Matrix (Fin 3) (Fin 3) OmegaField)ˣ =>
        (u : Matrix (Fin 3) (Fin 3) OmegaField)) hg9
  have hmat3 : (g : Matrix (Fin 3) (Fin 3) OmegaField) ^ 3 = 1 :=
    CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12.pow_three_eq_one_of_pow_nine hF hdet hmat9
  have hg3 : g ^ 3 = 1 := by
    apply Units.ext
    simpa using hmat3
  have hdvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
  rw [hord] at hdvd
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
