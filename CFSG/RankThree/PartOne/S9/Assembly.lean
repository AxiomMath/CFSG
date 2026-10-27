module

public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S9.StatementsSylow
import CFSG.RankThree.PartOne.S9.Top.Dichotomy
import CFSG.RankThree.PartOne.S9.Alpha.UniformVerification
import CFSG.RankThree.PartOne.S9.Planes.AlphaPlanes
import CFSG.RankThree.PartOne.S9.Sylow.ResidualProperSubgroup
import CFSG.RankThree.PartOne.S9.Sylow.ResidualTwoSubgroupTransfer
import CFSG.RankThree.PartOne.S9.Sylow.AlternativesPlaneCommutator
import CFSG.RankThree.PartOne.S9.Sylow.AlternativesSylowTwo
import CFSG.RankThree.PartOne.S9.Sylow.Exclusion
import CFSG.RankThree.PartOne.S9.Sylow.GlobalNormalKernel
import CFSG.RankThree.PartOne.S9.Sylow.GlobalTrivialAction
import CFSG.RankThree.PartOne.S9.Vanishing.AlphaZeroSylowCentralization
import CFSG.RankThree.PartOne.S9.Vanishing.AlphaZeroOddIntersection
import CFSG.RankThree.PartOne.S9.Vanishing.CoreVanishingDichotomy
import CFSG.RankThree.PartOne.S9.Extraction.InitialCritical
import CFSG.RankThree.PartOne.S9.Extraction.CentralizerConstrained
import CFSG.RankThree.PartOne.S9.QD32.PrimeSupport
import CFSG.RankThree.PartOne.S9.QD32.Geometry
import CFSG.RankThree.PartOne.S9.OddCore.RecognitionMain
import CFSG.RankThree.PartOne.S9.OddCore.RecognitionTwoLocal
import CFSG.RankThree.PartOne.S9.OddCore.RecognitionLifting
import CFSG.RankThree.PartOne.S9.OddCore.TorsionLifting
import CFSG.RankThree.PartOne.S9.MinTwoAction.FixedRankWithout
import CFSG.RankThree.PartOne.S9.MinTwoAction.LiftingElementary
import CFSG.RankThree.PartOne.S9.MinTwoAction.LiftingAlternatives
import CFSG.RankThree.PartOne.S9.MinTwoAction.LiftingSelected
import CFSG.RankThree.PartOne.S9.MinTwoAction.FiveActionRedMain

public section

namespace CFSG.RankThree.PartOne

theorem selectedPrimeDichotomy_of_residualBound (h8 : SectionEightResidualBound) :
    SelectedPrimeDichotomy := by
  have hPSR := properSubgroupResidual_of h8
  have hRTST := residualTwoSubgroupTransfer_of hPSR
  have hEFQKE := elementaryFaithfulQuotientKernelElimination
  have hMTASFQ := minimalTwoActionSmallFaithfulQuotient
  have hMTAWR3 := minimalTwoActionWithoutRankThreeFixedGroup_of hMTASFQ hEFQKE
  have hMTAA := minimalTwoActionAlternatives_of hMTASFQ hEFQKE
    (elementarySmallActionWholeGroupLifting_of hEFQKE) hMTAWR3
    minimalFiveActionSmallFieldKernelCentralization
  have hI1 := selectedPrimeMinimalTwoActionReduction_of hMTAA hMTASFQ hEFQKE
  have hI2 := twoLocalRankTwoOddCoreAction_of (criticalOddCoreTwoActionRecognition_of hMTAWR3)
    (extraspecialTwoActionOddCoreTorsionLifting_of extraspecialThirtyTwoFixedRankTwoAction)
  have hESAE := exceptionalSmallActionExclusion_of hRTST quaternionDihedralOddCentralizerGeometry
    quaternionDihedralAutomorphismPrimeSupport hI2
  have hCTCB := centralizerTwoCoreCommutatorBound_of hPSR centralizerConstrainedCriticalAction
    hI1 (smallOddCoreActionLiftingInsideLocalGroup_of hI2) hESAE
  have hTGTCA := trivialGlobalTwoCoreAction_of initialCriticalAction
    (normalOddCoreActionKernelCentralization_of hI1 hI2 hESAE) hRTST
  have hS2A := sylowTwoAlternatives_of initialCriticalAction hI1 hCTCB hTGTCA
  have hUAV := sectionNineUniformAlphaVerification_of hPSR
    (sectionNinePlaneCommutatorBound_of hPSR hS2A)
  have hAZSC := alphaZeroSylowCentralization_of hUAV hS2A
  have hAPCLN :=
    alphaProductCoreLocalNormalizer_of (alphaGlobalPlaneRelations_of alphaRankThreeLocalCompletion)
  exact selectedPrimeDichotomy_of_coreVanishing
    (coreVanishingDichotomy_of hUAV hAPCLN hAZSC (alphaZeroOddIntersection_of hPSR hAZSC))

end CFSG.RankThree.PartOne
