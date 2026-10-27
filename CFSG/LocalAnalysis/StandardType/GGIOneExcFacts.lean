module

public import CFSG.LocalAnalysis.StandardType.GGIOneExcE6
public import CFSG.LocalAnalysis.StandardType.GGIOneExcSmall
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeBstar
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE7

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggE6ThreeRankSixTwoLocal_holds :
    GGE6ThreeRankSixTwoLocal := by
  intro K _ _ n _ hK h3 E hEI hE hcard
  haveI : CharP K 2 := charP_two_of_card hK
  exact (TableBExc.E6Three.card_le_and_normalizes_E6_three K (by rw [hK]; exact h3) hE
    fun φ hφ => hEI hφ).2 hcard

theorem ggExcTwoCenterThreeInput_holds :
    GGExcTwoCenterThreeInput := by
  refine ⟨fun K _ _ hK => ?_, fun K _ _ hK => ?_, fun K _ _ hK => ?_⟩
  · haveI : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK]; norm_num)
    exact ExcSplitL.ggCenterPrime_recipe_E7 (f := 1) le_rfl (by rw [hK]; norm_num)
      Nat.prime_three (by norm_num)
  · haveI : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK]; norm_num)
    exact ExcSplitL.ggCenterPrime_recipe_E8 Nat.prime_three (by norm_num)
  · haveI : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK]; norm_num)
    exact ExcSplitL.ggCenterPrime_recipe_F4 Nat.prime_three (by norm_num)

end CFSG.StandardType

end
