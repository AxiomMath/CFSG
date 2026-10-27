module

public import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6
public import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6A6
public import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofONPoint
public import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofPGL

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13

theorem step148PointHJ_of_res
    (h143 : Concl143S14) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hGen : Step148PointHJdONGen) : Step148PointHJ :=
  Item148Point.step148PointHJ_of h143 (step148PointHJdONPoint_of h134 h48) hGen
    step148PointHJdA6_holds step148PointHJdA6A6_holds

theorem step148PGLImg_of_res
    (hN : Step148PGLNorm) (hK : KF148PGLInnerV) (hCe : Step148PGLCent) : Step148PGLImg :=
  step148PGLImg_of (step148PGLSplit_of hN hK) hCe

end CFSG.RankThree.PartTwo.Sec14
