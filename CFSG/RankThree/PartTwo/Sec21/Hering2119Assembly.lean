module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119Rank
public import CFSG.RankThree.PartTwo.Sec21.Item2129Res3ProofEnd

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Items

theorem item2119_of_steps12 (h211 : Item211) (h213 : Item213) (h214 : Item214)
    (h215 : Item215) (h218 : Item218) (h2115 : Item2115) (h2116 : Item2116) (h2118 : Item2118)
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h66 : Sec6.Item6_6) (hΩ : Item2120Omega)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hLoc : Item2125StarLocal) (hEnd : Item2119EndLoc) : Item2119 :=
  item2119_of_steps11 h211 h213 h214 h215 h218 h2115 h2116 h2118 h45 h48 h66 hΩ hLoc
    (item2126Loc_holds h211 h2115 h2116 h218 h2118 h45 h48 h66
      (item2125Star_of_local h45 h66 hLoc) h213 hGA) hEnd

end Items

end CFSG.RankThree.PartTwo.Sec21
