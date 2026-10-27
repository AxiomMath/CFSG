module

public import CFSG.RankThree.PartOne.KP.SporadicDefs
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M12
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.M24
public import CFSG.Sporadic.Schreier.J1Outer

public section

namespace CFSG.RankThree.PartOne

open CFSG
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem sporadicCoprimeRank_M11 : SporadicCoprimeRank .M11 :=
  sporadicCoprimeRank_of_card_outer_le (k := 2) (by norm_num)
    Sporadic.Schreier.at_m11_schreier.1

theorem sporadicCoprimeRank_M12 : SporadicCoprimeRank .M12 :=
  sporadicCoprimeRank_of_card_outer_le (k := 4) (by norm_num)
    Sporadic.Schreier.at_m12_schreier.1

theorem sporadicCoprimeRank_M22 : SporadicCoprimeRank .M22 :=
  sporadicCoprimeRank_of_card_outer_le (k := 4) (by norm_num)
    Sporadic.Schreier.at_m22_schreier.1

theorem sporadicCoprimeRank_M23 : SporadicCoprimeRank .M23 :=
  sporadicCoprimeRank_of_card_outer_le (k := 2) (by norm_num)
    Sporadic.Schreier.at_m23_schreier.1

theorem sporadicCoprimeRank_M24 : SporadicCoprimeRank .M24 :=
  sporadicCoprimeRank_of_card_outer_le (k := 4) (by norm_num)
    Sporadic.Schreier.at_m24_schreier.1

theorem sporadicCoprimeRank_J1 : SporadicCoprimeRank .J1 :=
  sporadicCoprimeRank_of_card_outer_le (k := 1) (by norm_num)
    Sporadic.Schreier.at_j1_schreier.1.le

end CFSG.RankThree.PartOne
