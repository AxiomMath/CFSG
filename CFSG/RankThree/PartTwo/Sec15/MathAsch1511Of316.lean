module

public import CFSG.RankThree.PartTwo.Sec15.Item156RDischarge

public section

namespace CFSG.RankThree.PartTwo.Sec15.Res1H1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15


theorem item1511R_of_item316
    (h316 : Sec19.Item316) : Item1511R := by
  have h48 := Sec11.Close.closed_sec4Item4_8
  have h134 := item134_holds
  have h148 := Ronan148M.item148R_holds
  have h149 := Ronan149.item149S14_holds
  have h142 := item142R_of_wired item142AllS14_holds
  have hcomp : Step152CompR := step152CompR_of_item148R h149 h148 h134 h48
    Sec4.Sporadic.rank3II_4_15 KFacts.kpSz
  have hexcl : Step152ExclR := step152ExclR_of (step152ExclSL2_of_item148HJ h134 h48
    (item148HJS14_of_wired Ronan148M.item148S14_holds))
  have h152 : Item152BigR := Ronan152Six.item152BigR_of
    Sec4.Census.rank3II_4_4_of_griess_noItem41 hcomp hexcl
  have h159 : Item159R := Ronan154Big.item159R_of_big154 item135_holds h316 h152
  exact item1511R_of_items h142 h148 rank3II_13_1a_narrow
    (rank3II_13_3_of rank3II_13_1_holds item4_22_holds Sec4.rank3II_4_5) h134 h48
    (item13SetupAt_of item4_22_holds Sec4.rank3II_4_5) LiebeckClosed.item158Y0R_holds h159
    item1510R_holds step169TwoBridge_holds

end CFSG.RankThree.PartTwo.Sec15.Res1H1
