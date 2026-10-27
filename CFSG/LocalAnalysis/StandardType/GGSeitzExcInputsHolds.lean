module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExc
public import CFSG.LocalAnalysis.StandardType.L34OvergroupInput
public import CFSG.LocalAnalysis.StandardType.SpEightOvergroupInput
public import CFSG.LocalAnalysis.StandardType.SpSixOvergroupInput
public import CFSG.LocalAnalysis.StandardType.TitsFiveOvergroup
public import CFSG.LocalAnalysis.StandardType.TitsThreeOvergroup

public section

namespace CFSG.StandardType

theorem ggSeitzExcInputs_holds :
    GGSeitzExcInputs := by
  unfold GGSeitzExcInputs
  exact ⟨ggSeitzExcUFourTwoInput_holds, ggSeitzExcTitsThreeInput_holds,
    ggSeitzExcTitsFiveInput_holds, ggSeitzExcSpEightOvergroupInput_holds,
    ggSeitzExcSpEightCentralizerInput_holds, ggSeitzExcSpSixOvergroupInput_holds,
    ggSeitzExcSpSixCentralizerInput_holds, ggSeitzExcLThreeFourOvergroupInput_holds,
    ggSeitzExcLThreeFourCentralizerInput_holds⟩

end CFSG.StandardType
