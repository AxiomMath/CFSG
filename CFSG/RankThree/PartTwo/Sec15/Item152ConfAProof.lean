module

public import CFSG.RankThree.PartTwo.Sec15.Item152ConfAProofD
public import CFSG.RankThree.PartTwo.Sec15.Item152ConfAProofP
public import CFSG.RankThree.PartTwo.Sec15.Item152ConfAProofT
public import CFSG.RankThree.PartTwo.Sec15.Item152ConfAProofTheta

public section

namespace CFSG.RankThree.PartTwo.Sec15

theorem step152ConfR_of_confA
    (h142 : Sec14.Item142R) (hperm : Step152ConfTPermR) (hle : Step152ConfThetaLeR)
    (hnorm : Step152ConfThetaNormR) (hPS : Step152ConfPSR) (hF : Step152ConfFR)
    (hW : Step152ConfWR) : Step152ConfR :=
  step152ConfR_of (step152ConfDR_of h142) step152ConfPR_of (step152ConfTR_of hperm)
    (step152ConfThetaR_of hle hnorm) hPS hF hW

end CFSG.RankThree.PartTwo.Sec15
