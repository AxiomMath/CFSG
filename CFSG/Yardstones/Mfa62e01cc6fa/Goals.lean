module

public import CFSG.Yardstones.Mfa62e01cc6fa.Definitions
public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.CanonicalRoute
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82KStatements
import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TFinal
import CFSG.LocalAnalysis.ComponentClassification.Foote1978.FooteTypeMaximalRoute

public section

namespace CFSG.Yardstones.Mfa62e01cc6fa

open CFSG.ComponentClassification

theorem ys01_solomon75LocalStructure :
    OddStandard.Solomon75.Solomon75LocalStructure :=
  CFSG.OddStandard.Solomon75.localStructure_of_solomon2AnInput
    (CFSG.OddStandard.Solomon75.solomon2AnInput_of_gh74Milestone
      @CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models)

theorem ys02_altStdCyclicOddTwoFalse :
    SolAltLit.AltStdCyclicOddTwoFalse :=
  CFSG.OddStandard.AltStdCycTwo.altStdCyclicOddTwoFalse_holds

theorem ys03_swapMemberResidueNineExact :
    SolMax.SwapP2.SwapMemberResidueNineExact :=
  CFSG.ComponentClassification.SolMax.SwapP2.ys06_of_exactGenerationInput
    CFSG.ComponentClassification.SolMax.SwapP2.exactGenerationInput_holds

theorem ys04_swapMemberResidueNineExoticT2 :
    SolMax.SwapP2.SwapMemberResidueNineExoticT2 :=
  CFSG.ComponentClassification.SolMax.SwapP2.ys07_closed

theorem ys05_swapMemberResidueNineExoticT3 :
    SolMax.SwapP2.SwapMemberResidueNineExoticT3 :=
  CFSG.ComponentClassification.SolMax.SwapP2.ys08_closed

theorem ys06_signalizerNineSixDihedralLocalInput : SolMax.SignalizerNineSixDihedralLocalInput :=
  SolMax.signalizerNineSixDihedralLocalInput_holds

theorem ys09_footeMaximalUnbalancedInput :
    FooteLit.FooteMaximalUnbalancedInput :=
  CFSG.ComponentClassification.FooteLit.footeMaximalUnbalancedInput_of_rankIncrease
    CFSG.ComponentClassification.FooteLit.footeRankIncrease_holds

theorem ys08_griessSolomonInput
    : GSLit.GriessSolomonInput := by
  exact CFSG.ComponentClassification.GS79bSec5.griessSolomonInput_of_canonicalRoute
    ys09_footeMaximalUnbalancedInput



theorem ys11_gs82CentXA10TransferInput :
    GSThmB.GS82CentXA10TransferStatementK :=
  CFSG.ComponentClassification.GSThmB.A10T.gs82CentXA10TransferStatementK_holds

theorem ys12_gs82Step2FuseInput :
    GSThmB.GS82Step2FuseStatementK :=
  CFSG.ComponentClassification.GSThmB.gs82Step2FuseStatementK_holds

theorem ys13_lemma39TwoDiscK2Hub :
    Lemma39TwoDiscK2Hub :=
  Sol76.Sig.GSYard03.lemma39TwoDiscK2At_solRestrictedHub_holds

theorem ys14_quasisimpleSylowFourJoinedSCN :
    Sol76.Sig.QuasisimpleSylowFourJoinedSCN :=
  Sol76.Sig.GSYard02.quasisimpleSylowFourJoinedSCN_holds

theorem ys15_solomonQTwoDisconnectedSylowInvFor :
    Sol76.Sig.SolomonQTwoDisconnectedSylowInvFor :=
  Sol76.Sig.GSYard03.solomonQTwoDisconnectedSylowInvFor_holds

end CFSG.Yardstones.Mfa62e01cc6fa
