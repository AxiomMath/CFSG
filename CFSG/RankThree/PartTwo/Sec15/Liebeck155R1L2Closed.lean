module

public import CFSG.RankThree.PartTwo.Sec15.Praeger155R1L2Route150
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150Holds

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec15.Sylow155R1
  CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.LocalRank


theorem res1ZExclLeN_l2_a7_of_316
    (h316 : Sec19.Item316) :
    Res1ZExclLeN (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) Res1OpenL2Type :=
  res1ZExclLeN_l2_a7 h316 Liebeck155R1T150.res1Thm150b_a7

theorem res1ZExclLeN_l2_m22_of_316
    (h316 : Sec19.Item316) :
    Res1ZExclLeN (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22))
      Res1OpenL2Type :=
  res1ZExclLeN_l2_m22 h316 Liebeck155R1T150.res1Thm150b_m22

end CFSG.RankThree.PartTwo.Sec15
