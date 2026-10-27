module

public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4Chief
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityRest

public section

namespace CFSG.StandardType

theorem ggSixStepThreeCInput_of_reeB2Module (hM : GGReeB2ModuleFixedInput) :
    GGSixStepThreeCInput :=
  ggSixStepThreeCInput_of_F4 (ggSixStepThreeCFourInput_of_reeB2Module hM)

end CFSG.StandardType
