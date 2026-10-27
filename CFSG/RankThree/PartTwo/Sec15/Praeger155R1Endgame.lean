module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1L3Odd
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3Item1730
public import CFSG.RankThree.PartTwo.Sec15.Lempken155L3NotLe

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.PartTwo.Sec6 CFSG.RankThree.PartTwo.Sec19
  CFSG.RankThree.PartTwo.Sec15.Sylow155R1 CFSG.RankThree.PartTwo.Sec15.LempkenL3
  CFSG.RankThree.PartTwo.Sec15.Liebeck155R1L3T150

theorem res1L112InPt_l3Pt_of_316_of_cover
    (h316 : Sec19.Item316)
    (hcov : Res1Omega1513.Res1CoverL3) :
    Sylow155R1.Res1L112InPt Res1L3Pt Res1OpenType :=
  LempkenL3.res1L112InPt_l3Pt_of_even_odd (LempkenL3.res1L112InPt_l3Even_of_cover h316 hcov)
      (Sylow155R1.L3Odd.res1L112InPt_l3Odd_of_316 h316)

theorem item1730_of_316_310_cover
    (h316 : Sec19.Item316) (h310 : Sec6.Item3_10)
    (hcov : Res1Omega1513.Res1CoverL3) : Sec17.Item1730 :=
  item1730_of_316_310_in h316 h310 (res1L112InPt_l3Pt_of_316_of_cover h316 hcov)

end CFSG.RankThree.PartTwo.Sec15
