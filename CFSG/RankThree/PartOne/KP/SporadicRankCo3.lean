module

public import CFSG.RankThree.PartOne.KP.SporadicDefs
public import CFSG.RankThree.PartOne.KP.Co3Aut

public section

namespace CFSG.RankThree.PartOne

open CFSG
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem sporadicCoprimeRank_Co3 : SporadicCoprimeRank .Co3 :=
  sporadicCoprimeRank_of_card_outer_le (k := 1) (by norm_num)
    CTUC_Co3_all_automorphisms_inner.{0}.2.2.2.1.le

end CFSG.RankThree.PartOne
