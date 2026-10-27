module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeExcPlusAux2
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitE6Two
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwo
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6TwoThree

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.RootSystem CFSG.LieType.SeitzGeneration

theorem ggWTEx1_weylTypeW_E6Two_three
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    GGTorusWeylTypeW 3 4 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) := by
  haveI : CharP K 2 := charP_two_of_card (K := K) (m := 1) (by rw [pow_one]; exact hK)
  exact ggWTEx1_weylTypeW_of_excPlusModel Nat.prime_three (by norm_num)
    ggWTEx1_isWeylMatrix_F4 ggWTEx1_card_F4
    (ggExcPlusWeylModelSCr_of_frameModelOn Nat.prime_three
      (TableBExc.center_recipeGroup_eq_bot .E6 K)
      (fun φ hφ _ => TableBExc.E6Three.recipeID_subset_inn_E6_two hK hφ)
      (ggCenterPrime_recipe_E6_two hK Nat.prime_three)
      ((excPlusFrameModelOn_E6Two_three hK).of_mulEquiv (TableBExc.recipeEquiv .E6 K)))

end CFSG.StandardType

end
