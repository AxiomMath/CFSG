module

public import CFSG.RankThree.PartTwo.Sec21.Item21Late2Proof2120

public section

namespace CFSG.RankThree.PartTwo.Sec21

theorem item2119_of_items
    (h211 : Item211) (h2115 : Item2115) (h2116 : Item2116)
    (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (hΩ : Item2120Omega) (hEnd : Item2119End) :
    Item2119 :=
  item2119_of h211 h2115 h2116 (item2119Frame_of h45 h66) (item2120_of h45 h66 hΩ)
    (item2121_of h45 h66) hEnd

end CFSG.RankThree.PartTwo.Sec21
