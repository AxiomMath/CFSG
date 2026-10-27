module

public import CFSG.RankThree.PartTwo.Sec8.Hering88CCent
public import CFSG.RankThree.PartTwo.Sec8.Hering88CFive
public import CFSG.RankThree.PartTwo.Sec8.Hering88CTwo
import CFSG.RankThree.PartTwo.Sec8.Item84KFacts4ProofSp4
import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.RankThree.PartTwo.Sec8

namespace Hering88C

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem inputs47ClassesD4_holds :
    Sec4.Inputs47ClassesD4 :=
  inputs47ClassesD4_of_lang kF82D4LangCoset_holds kF82D4SecondCent_holds

theorem kF88StepDCaseTwo_holds
    (h45 : Sec4.Item4_5) (h84 : Pair84A) (hF : KF84Field) : KF88StepDCaseTwo :=
  kF88StepDCaseTwo_of h45 (kF88SwapCent_holds h45 h84) hF

theorem kF88StepDCaseFive_holds
    (h45 : Sec4.Item4_5) (h84 : Pair84A) (hF : KF84Field) : KF88StepDCaseFive :=
  kF88StepDCaseFive_of h45 (kF88SwapCent_holds h45 h84) hF Item84KFacts4.kF84Sp4ThreeCent_holds

end Hering88C

end CFSG.RankThree.PartTwo.Sec8
