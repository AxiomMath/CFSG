module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res6ProofFieldTop
import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofSubfield
import CFSG.CGT.PushingUpLit.Transport
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.LocalRank CFSG.GH74.GLS

theorem step148RankImg_of_notK (hNotK : Step148RankImgGeFieldTopNotK) : Step148RankImg :=
  step148RankImg_of (step148RankImgLe_of step148RankImgLeEq_holds)
    (step148RankImgGe_of (step148RankImgGeField_of_top
      (step148RankImgGeFieldTop_of_dich
        (step148RankImgGeFieldTopDich_of Item148Res8.kf148SubfieldOver_holds) hNotK)))

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
