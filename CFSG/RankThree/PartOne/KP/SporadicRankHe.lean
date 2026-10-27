module

public import CFSG.RankThree.PartOne.KP.SporadicDefs
public import CFSG.Sporadic.Schreier.PairHePairs

public section

namespace CFSG.RankThree.PartOne

open CFSG
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem sporadicCoprimeRank_He : SporadicCoprimeRank .He :=
  sporadicCoprimeRank_of_card_outer_le (k := 2) (by norm_num)
    Sporadic.Schreier.AT_He_Schreier.1

end CFSG.RankThree.PartOne
