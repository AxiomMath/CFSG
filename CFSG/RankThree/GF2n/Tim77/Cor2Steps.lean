module

public import CFSG.RankThree.GF2n.Tim81.RonanInputsHolds
public import CFSG.RankThree.GF2n.Tim77.Sec31
public import CFSG.RankThree.GF2n.Tim77.Sec34
public import CFSG.RankThree.GF2n.Tim77.Sec35
public import CFSG.RankThree.GF2n.Tim77.Sec54
public import CFSG.RankThree.GF2n.Tim77.Cor2AlphaHolds
public import CFSG.RankThree.GF2n.Tim77.Cor2BetaInner
public import CFSG.RankThree.GF2n.Tim77.Cor2BetaComponents

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75

theorem tim77Cor2_of_remaining
    (h33 : Tim77Sec33Statement) (h43 : Tim77Sec43Statement) (h44 : Tim77Sec44Statement)
    (h415 : Tim77Sec415Statement) (h53 : Tim77Sec53Statement) :
    CFSG.RankThree.GF2n.Stroth80.Tim77Cor2Statement :=
  tim77Cor2_of_leaves theoremAStmt_holds
    { exNotation := tim77ExistsNotation_holds
      sec31 := tim77Sec31_holds
      sec33 := h33
      sec34 := tim77Sec34_holds
      sec35 := tim77Sec35_holds
      sec415 := h415
      sec54 := sec54_of h53 h43 h44 tim77Sec35_holds
      alpha := tim77AlphaBox_holds
      beta := tim77BetaBox_of_componentData goldschmidt1974_of_milestone
          (cor2Beta_componentData_holds goldschmidt1974_of_milestone) }

end CFSG.RankThree.GF2n.Tim77
