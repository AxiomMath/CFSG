module

public import CFSG.RankThree.PartTwo.Sec15.Item152GenProofTheta
public import CFSG.RankThree.PartTwo.Sec15.Item152GenProofS
public import CFSG.RankThree.PartTwo.Sec15.Item152GenProofXCover
public import CFSG.RankThree.PartTwo.Sec15.KS152Named

public section

namespace CFSG.RankThree.PartTwo.Sec15

theorem ks152HJGen_holds_of
    (hK : KS152J2InvolNine) (hcov : Step152GenXCover) : KS152HJGen :=
  kS152HJGen_of step152GenTheta_holds (step152GenS_of hK) (step152GenX_of hcov) ks152J2Gen_holds

theorem step152GenX_of_item142
    (h142 : Sec14.Item142AllS14) : Step152GenX :=
  step152GenX_of (step152GenXCover_of h142)

theorem ks152HJGen_holds_of_item142
    (hK : KS152J2InvolNine) (h142 : Sec14.Item142AllS14) : KS152HJGen :=
  ks152HJGen_holds_of hK (step152GenXCover_of h142)

end CFSG.RankThree.PartTwo.Sec15
