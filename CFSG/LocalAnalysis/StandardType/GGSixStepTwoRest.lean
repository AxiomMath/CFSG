module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoRestAutK
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoRestCent

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

open CFSG.LocalAnalysis.ComponentInitial in
theorem ggSixStepTwoV2Input_of_rest (hSch : SchreierFor InCatalog)
    (h613 : GGStepTwoLemmaSixThirteenInput) (hA : GGStepTwoLinearFusionInput)
    (hKF : GGKGroupFusionLayerInput) (hRat : GGSixAutKHypRestAtInput)
    (h5 : GGStepTwoAutKFiveInput) (h3 : GGStepTwoAutKThreeInput)
    (hidx : GGStepTwoBstarIndexInput) (hwit : GGStepTwoContraryWitnessInput)
    (hX : GGStepTwoContraryXInput) (hN : GGStepTwoContraryNormalizerInput) :
    GGSixStepTwoV2Input := by
  have hR : GGStepTwoAutKRestInput := ggStepTwoAutKRestInput_of_finer hRat h5 h3
  have h614 : GGStepTwoSubnormalInput :=
    ggStepTwoSubnormalInput_of_split (ggLemmaThreeFourteenInput_of_schreier hSch)
      (ggStepTwoComponentInput_of_kgroupLayer ggLemmaThreeThirteenInput_holds hKF hR)
  exact ggSixStepTwoV2Input_of_schreierLayer hSch h613 hA hKF hR
    (ggStepTwoCentralizerInput_of_rest h613 h614 hidx hwit hX hN)

end Inputs

end CFSG.StandardType
