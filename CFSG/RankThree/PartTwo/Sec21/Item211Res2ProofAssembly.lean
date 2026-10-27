module

public import CFSG.RankThree.PartTwo.Sec21.Item211ResProofSplit
public import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofInner
public import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofLocal

public section

namespace CFSG.RankThree.PartTwo.Sec21

section Certs

theorem item2130_of_res2
    (h211 : Item211) (h213 : Item213) (h217 : Item217) (h218 : Item218) (h2115 : Item2115)
    (h2116 : Item2116) (h2117 : Item2117) (h2118 : Item2118) (h2119 : Item2119)
    (hNF : Item211NoField) (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (hin : Sec4.Inputs47NoD4) (h3 : Item2130LocalThree) (hch : Item2130LocalChoice)
    (hON : Item2130LocalON) (hT : Item2130LocalTypes) : Item2130 :=
  item2130_of_lStar_local h2115
      (item2130LStar_of h211 h213 h217 h218 h2116 h2117 h2118 h2119 hNF
          (item2130LStarInner_of h45 h66 hin)) (item2130Local_of h3 hch hON hT)

end Certs

end CFSG.RankThree.PartTwo.Sec21
