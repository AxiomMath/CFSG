module

public import CFSG.RankThree.PartTwo.Sec21.Item2129Res3ProofAssembly
public import CFSG.RankThree.PartTwo.Sec21.Item2119End8ProofAssembly

public section

namespace CFSG.RankThree.PartTwo.Sec21

section Items

theorem item2119_of_steps11 (h211 : Item211) (h213 : Item213) (h214 : Item214)
    (h215 : Item215) (h218 : Item218) (h2115 : Item2115) (h2116 : Item2116) (h2118 : Item2118)
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h66 : Sec6.Item6_6) (hΩ : Item2120Omega)
    (hLoc : Item2125StarLocal) (h2126 : Item2126Loc) (hEnd : Item2119EndLoc) : Item2119 :=
  item2119_of_steps9 h211 h214 h215 h218 h2115 h2116 h2118 h45 h48 h66 hΩ hLoc h2126
    (item2129S_of_itemsLocal h211 h2115 h2116 h218 h2118 h45 h48 h66 hLoc h213) hEnd

end Items

end CFSG.RankThree.PartTwo.Sec21
