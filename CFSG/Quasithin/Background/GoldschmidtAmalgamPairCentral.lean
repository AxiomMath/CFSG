module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamPairBasic
public import CFSG.Quasithin.Recognition.Gold2Central

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem goldschmidtCentralAbelianBound_of_charTwoLargePair
    (h : F6.GoldschmidtCharTwoLargePair.{0}) : GoldschmidtCentralAbelianBound := by
  intro G _ _ I₁ I₂ z he₁ he₂ h₁ h₂ c₁ c₂ hO _ _ _ _ _ _ _
  have hp : F6.IsGoldschmidtVPair I₁ I₂ := ⟨he₁, he₂, h₁, h₂, hO⟩
  exact (F6.card_inf_le_two_pow_seven_of_charTwoLargePair h hp c₁ c₂).trans (by norm_num)

end CFSG.Quasithin
