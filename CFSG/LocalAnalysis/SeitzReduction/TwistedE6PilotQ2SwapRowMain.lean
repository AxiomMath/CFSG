module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2SwapRow
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2SwapRowTri
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2SwapRowOverlap

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)
open CFSG.SeitzReduction.OmegaPilot (OmegaNotOddLieInputAt)

theorem twistedE6TwoSwapRowInput_of_overlapFacts (hO : TwistedE6TwoOverlapFacts) :
    TwistedE6TwoSwapRowInput :=
  twistedE6TwoSwapRowInput_of_triangle (twistedE6TwoTriangleInput_of_overlapFacts hO)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem twistedE6TwoSwapRowInput_holds : TwistedE6TwoSwapRowInput :=
  twistedE6TwoSwapRowInput_of_overlapFacts twistedE6TwoOverlapFacts_holds

end CFSG.SeitzReduction.TwistedE6Pilot
