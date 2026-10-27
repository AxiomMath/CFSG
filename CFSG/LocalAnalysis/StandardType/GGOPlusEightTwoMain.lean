module

public import CFSG.LocalAnalysis.StandardType.GGOPlusEightTwoTri
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveOrthPlus

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Certs


theorem ggIOneOrthPlusFourInput_of_midClass (hmid : OPlusEight.MidClassInput) :
    GGIOneOrthPlusFourInput := by
  intro K _ _ hK
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      le_rfl hK'
  have hAll : GGEndNodeRootEltAll 3 3 (OrthRest.RPlus K 4) :=
    OPlusEight.ggEndNodeRootEltAll_of_mulEquiv
      (RecipeFieldOmega.plusEquiv (K := K) (m := 4) (by norm_num)).symm
      (OPlusEight.ggEndNodeRootEltAll_om8 hK hmid)
  obtain ⟨hZ, hC⟩ := ggOrthRestCenterInput_holds.2 K 4 hK le_rfl
  exact ggEndNodeIOne_of_eltAll (fun _ hφ _ => hφ) hZ hC hAll

theorem ggIOneOrthPlusFourInput_of_midClassSolvable (h : OPlusEight.MidClassSolvableInput) :
    GGIOneOrthPlusFourInput :=
  ggIOneOrthPlusFourInput_of_midClass (OPlusEight.midClassInput_of_solvable h)

theorem ggIOneOrthPlusFourInput_of_midClassCommute (h : OPlusEight.MidClassCommuteInput) :
    GGIOneOrthPlusFourInput :=
  ggIOneOrthPlusFourInput_of_midClassSolvable (OPlusEight.midClassSolvableInput_of_commute h)

end Certs

end CFSG.StandardType

end
