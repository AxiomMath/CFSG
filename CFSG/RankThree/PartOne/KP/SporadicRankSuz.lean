module

public import CFSG.RankThree.PartOne.KP.SporadicDefs
public import CFSG.Sporadic.SuzOddCore.Outer

public section

namespace CFSG.RankThree.PartOne

open CFSG
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem sporadicCoprimeRank_Suz : SporadicCoprimeRank .Suz :=
  sporadicCoprimeRank_of_card_outer_le (k := 2) (by norm_num)
    Sporadic.SuzOddCore.outer_carrier_suz.1.le

end CFSG.RankThree.PartOne
