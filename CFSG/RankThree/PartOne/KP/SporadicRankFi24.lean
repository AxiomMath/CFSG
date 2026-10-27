module

public import CFSG.RankThree.PartOne.KP.SporadicDefs
public import CFSG.Sporadic.Schreier.Fi24Schreier

public section

namespace CFSG.RankThree.PartOne

open CFSG
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem sporadicCoprimeRank_Fi24Prime : SporadicCoprimeRank .Fi24Prime :=
  sporadicCoprimeRank_of_card_outer_le (k := 2) (by norm_num)
    Sporadic.Schreier.Fi24.card_outer_fi24prime.le

end CFSG.RankThree.PartOne
