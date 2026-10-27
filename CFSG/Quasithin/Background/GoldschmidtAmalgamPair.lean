module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamPairBasic
public import CFSG.Quasithin.Background.GoldschmidtAmalgamSplit

public section

universe u

namespace CFSG.Quasithin

namespace F6

theorem goldschmidtCharTwoLarge_of_pair (h : GoldschmidtCharTwoLargePair.{u}) :
    GoldschmidtCharTwoLarge.{u} := by
  intro D _ _ G₁ G₂ hA c₁ c₂ hcard
  exact h D G₁ G₂ hA.toVPair c₁ c₂ hcard

end F6

end CFSG.Quasithin
