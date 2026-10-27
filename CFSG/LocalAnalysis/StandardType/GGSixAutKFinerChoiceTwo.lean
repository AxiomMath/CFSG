module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoSp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Rest

@[expose] def GGStepTwoChoiceThreeTwoRestSeven : Prop :=
  GGStepTwoChoiceThreeTwoTag .POmegaPlus ∧ GGStepTwoChoiceThreeTwoTag .POmegaMinus ∧
    GGStepTwoChoiceThreeTwoTag .F4 ∧ GGStepTwoChoiceThreeTwoTag .E6 ∧
      GGStepTwoChoiceThreeTwoTag .E7 ∧ GGStepTwoChoiceThreeTwoTag .E8 ∧
        GGStepTwoChoiceThreeTwoTag .twistedE6

theorem ggStepTwoChoiceThreeTwoRest_of_seven (h : GGStepTwoChoiceThreeTwoRestSeven) :
    GGStepTwoChoiceThreeTwoRest :=
  ⟨ggStepTwoChoiceThreeTwoTag_PSp, h⟩

end Rest

end CFSG.StandardType
