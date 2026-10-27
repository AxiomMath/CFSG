module

public import CFSG.RankThree.PartOne.KP.SporadicDefs
public import CFSG.Sporadic.Schreier.PairJ2Pairs
public import CFSG.Sporadic.Schreier.PairJ3Pairs
public import CFSG.Sporadic.Schreier.PairHSPairs

public section

namespace CFSG.RankThree.PartOne

open CFSG
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem sporadicCoprimeRank_J2 : SporadicCoprimeRank .J2 :=
  sporadicCoprimeRank_of_card_outer_le (k := 2) (by norm_num)
    Sporadic.Schreier.AT_J2_Schreier.1

theorem sporadicCoprimeRank_J3 : SporadicCoprimeRank .J3 :=
  sporadicCoprimeRank_of_card_outer_le (k := 6) (by norm_num)
    Sporadic.Schreier.AT_J3_Schreier.1

theorem sporadicCoprimeRank_HS : SporadicCoprimeRank .HS :=
  sporadicCoprimeRank_of_card_outer_le (k := 24) (by norm_num)
    Sporadic.Schreier.AT_HS_Schreier.1

end CFSG.RankThree.PartOne
