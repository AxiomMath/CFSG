module

public import CFSG.RankThree.PartOne.KP.SporadicDefs
public import CFSG.Sporadic.FischerOddCore.Fi23Aut

public section

namespace CFSG.RankThree.PartOne

open CFSG
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem sporadicCoprimeRank_Fi23 : SporadicCoprimeRank .Fi23 :=
  sporadicCoprimeRank_of_card_outer_le (k := 1) (by norm_num)
    Sporadic.FischerOddCore.CTUC_Fi23_Schreier.1.le

end CFSG.RankThree.PartOne
