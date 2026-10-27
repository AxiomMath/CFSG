module

public import CFSG.RankThree.PartTwo.Sec9.Item95
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiCTri
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiCTorus
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiCField
import CFSG.RankThree.PartTwo.Sec9.NotLTwoEight

public section

namespace CFSG.RankThree.PartTwo.Sec9

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem slPiTrichotomy : SLPiTrichotomy := fun _ _ _ _ _ hn hL _ hxN hx3 =>
  KFacts.inducesStdKind_trichotomy_of_isSLThreePiAt hn hL hxN hx3

theorem slPiTorusCent : SLPiTorusCent := fun _ _ _ _ hn hX _ hw3 hw _ _ hy hz =>
  KFacts.commute_of_mem_centralizer_of_isSLThreePiAt hn hX hw3 hw hy hz

theorem slPiFieldCent : SLPiFieldCent := fun _ _ _ _ _ hn hL _ haN ha3 ha =>
  KFacts.barCentralizer_facts_of_field hn hL haN ha3 ha

theorem item95_of_item45 (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) : Item95 :=
  item95_of h45 h48 slPiFieldCent slPiTrichotomy slPiTorusCent

theorem item96_of_item48
    (h82 : Sec8.Item82One) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) : Item96 :=
  item96_of_item95 h82 (item95_of_item45 h45 h48) h45 (notLTwoEight_of h45)

theorem item97_of_item48
    (h82 : Sec8.Item82One) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) : Item97 :=
  item97_of (item96_of_item48 h82 h45 h48) h45

end CFSG.RankThree.PartTwo.Sec9
