module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3Closed
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L2Closed
public import CFSG.RankThree.PartTwo.Sec15.Praeger155R1Item1730
public import CFSG.RankThree.PartTwo.Sec15.Gagen155BigHostClosed

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec15.Sylow155R1
  CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.LocalRank CFSG.PGLModel

theorem item159R_of_h316
    (h316 : Sec19.Item316) : Item159R :=
  Ronan154Big.item159R_of_big154 CFSG.RankThree.PartTwo.item135_holds h316
    (Ronan152Six.item152BigR_of Sec4.Census.rank3II_4_4_of_griess_noItem41
      (step152CompR_of_item148R Ronan149.item149S14_holds Ronan148M.item148R_holds
        CFSG.RankThree.PartTwo.item134_holds Close.closed_sec4Item4_8
        Sec4.Sporadic.rank3II_4_15 KFacts.kpSz)
      (step152ExclR_of (step152ExclSL2_of_item148HJ CFSG.RankThree.PartTwo.item134_holds
        Close.closed_sec4Item4_8
        (item148HJS14_of_wired Ronan148M.item148S14_holds))))

theorem item1730_of_l3Pt_316
    (h316 : Sec19.Item316) (h310 : Sec6.Item3_10)
    (hL3 : Step155HostE0WRes1TypeFPt Res1L3Pt Res1OpenType) : Sec17.Item1730 :=
  item1730_of_l3Pt h316 h310 hL3
    (step155HostE0WRes1TypeFBar_a7_split h316
      (res1ZExclLeN_l2_a7_of_316 h316)
      (Sylow155R1.res1ZExclLeN_su3_a7_of_316 h316))
    (step155HostE0WRes1TypeFBar_m22_split h316 (item159R_of_h316 h316)
      (res1ZExclLeN_l2_m22_of_316 h316)
      (Sylow155R1.res1ZExclLeN_su3_m22_of_316 h316))

end CFSG.RankThree.PartTwo.Sec15
