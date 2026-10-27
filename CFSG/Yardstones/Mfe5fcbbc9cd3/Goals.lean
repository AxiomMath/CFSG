module

public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.CanonicalRoute
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82KStatements
import CFSG.LocalAnalysis.ComponentClassification.GS82Step2L34Free
import CFSG.LocalAnalysis.ComponentClassification.Foote1978.FooteTypeMaximalRoute

public section

namespace CFSG.Yardstones.Mfe5fcbbc9cd3

open CFSG.ComponentClassification

theorem ys01_lemma39TwoDiscK2At_hub :
    Sol76.Sig.Lemma39TwoDiscK2At Sol76.Sig.solRestrictedHub :=
  Sol76.Sig.GSYard03.lemma39TwoDiscK2At_solRestrictedHub_holds

theorem ys02_quasisimpleSylowFourJoinedSCN :
    Sol76.Sig.QuasisimpleSylowFourJoinedSCN :=
  Sol76.Sig.GSYard02.quasisimpleSylowFourJoinedSCN_holds

theorem ys03_solomonQTwoDisconnectedSylowInvFor :
    Sol76.Sig.SolomonQTwoDisconnectedSylowInvFor :=
  Sol76.Sig.GSYard03.solomonQTwoDisconnectedSylowInvFor_holds

theorem ys04_solomon2An :
    GSThmB.Solomon2AnInput :=
  CFSG.OddStandard.Solomon75.solomon2AnInput_of_gh74Milestone
    @CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models

theorem ys05_altStdCyclicOddTwoFalse :
    SolAltLit.AltStdCyclicOddTwoFalse :=
  CFSG.OddStandard.AltStdCycTwo.altStdCyclicOddTwoFalse_holds

theorem ys06_swapMemberResidueNineExact :
    SolMax.SwapP2.SwapMemberResidueNineExact :=
  CFSG.ComponentClassification.SolMax.SwapP2.ys06_of_exactGenerationInput
    CFSG.ComponentClassification.SolMax.SwapP2.exactGenerationInput_holds

theorem ys07_swapMemberResidueNineExoticT2 :
    SolMax.SwapP2.SwapMemberResidueNineExoticT2 :=
  CFSG.ComponentClassification.SolMax.SwapP2.ys07_closed

theorem ys08_swapMemberResidueNineExoticT3 :
    SolMax.SwapP2.SwapMemberResidueNineExoticT3 :=
  CFSG.ComponentClassification.SolMax.SwapP2.ys08_closed

theorem ys09_signalizerNineSixDihedralLocal : SolMax.SignalizerNineSixDihedralLocalInput :=
  SolMax.signalizerNineSixDihedralLocalInput_holds

theorem ys13_footeMaximalUnbalancedInput :
    FooteLit.FooteMaximalUnbalancedInput :=
  CFSG.ComponentClassification.FooteLit.footeMaximalUnbalancedInput_of_rankIncrease
    CFSG.ComponentClassification.FooteLit.footeRankIncrease_holds

theorem ys12_griessSolomonInput
    : GSLit.GriessSolomonInput := by
  exact CFSG.ComponentClassification.GS79bSec5.griessSolomonInput_of_canonicalRoute
    ys13_footeMaximalUnbalancedInput

theorem ys14_gs82CentXA10Transfer :
    GSThmB.GS82CentXA10TransferStatementK :=
  CFSG.ComponentClassification.GSThmB.A10T.gs82CentXA10TransferStatementK_holds

theorem ys15_gs82Step2Fuse :
    GSThmB.GS82Step2FuseStatementK :=
  CFSG.ComponentClassification.GSThmB.gs82Step2FuseStatementK_holds

end CFSG.Yardstones.Mfe5fcbbc9cd3
