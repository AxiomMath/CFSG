module

public import CFSG.RankThree.PartTwo.Sec21.Item228InspProofSL3E27
public import CFSG.RankThree.PartTwo.Sec21.Item228InspProofSp4Transport
public import CFSG.RankThree.PartTwo.Sec21.Item228InspProofU54Transport

public section

namespace CFSG.RankThree.PartTwo.Sec21

open Item228InspProof

theorem insp228U4 (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (h222 : Item222)
    (hKW : KOfWellDefinedAll) : Insp228U4 :=
  insp228U4_of h45 h66 h222 hKW u4EvenTorus

theorem insp228U4Half (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (h222 : Item222)
    (hKW : KOfWellDefinedAll) : Insp228U4Half :=
  insp228U4Half_of h45 h66 h222 hKW u4EvenTorus

theorem insp228U54 (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (h222 : Item222)
    (hKW : KOfWellDefinedAll) : Insp228U54 :=
  insp228U54_of h45 h66 h222 hKW u4EvenTorus u54Torus


theorem insp228Sp4 (hNF : Item228NoFieldThree) (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (h222 : Item222) (hKW : KOfWellDefinedAll) : Insp228Sp4 :=
  insp228Sp4_of hNF h45 h66 h222 hKW sp4EvenTorus

theorem insp228SL3 (hNF : Item228NoFieldThree) (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (h222 : Item222) (hKW : KOfWellDefinedAll) (hSL : SL3E27) : Insp228SL3 :=
  insp228SL3_of h222 hKW (insp228SL3NonComm_of hNF h45 h66 h222 hKW hSL)

theorem item228Inspection_of (hNF : Item228NoFieldThree) (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) (h222 : Item222) (hKW : KOfWellDefinedAll) (hSL : SL3E27) :
    Item228Inspection :=
  item228Inspection_of_families (insp228SL3 hNF h45 h66 h222 hKW hSL)
    (insp228Sp4 hNF h45 h66 h222 hKW) (insp228U4 h45 h66 h222 hKW)
    (insp228U4Half h45 h66 h222 hKW) (insp228U54 h45 h66 h222 hKW)

end CFSG.RankThree.PartTwo.Sec21
