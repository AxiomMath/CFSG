module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmTag
public import CFSG.LocalAnalysis.StandardType.GGAssemblyEightDefs

public section

namespace CFSG.StandardType

section CompLift

theorem ggNonsplitCompLiftRound8_of_exc (hF4 : GGNonsplitCompLiftTag .F4)
    (hE6 : GGNonsplitCompLiftTag .E6) (hE7 : GGNonsplitCompLiftTag .E7)
    (hE8 : GGNonsplitCompLiftTag .E8) (hTwE6 : GGNonsplitCompLiftTag .twistedE6) :
    GGNonsplitCompLiftRound8 :=
  ⟨ggNonsplitCompLiftTag_POmegaPlus, ggNonsplitCompLiftTag_POmegaMinus, hF4, hE6, hE7, hE8,
    hTwE6⟩

end CompLift

section Marking

theorem ggNonsplitNbrMarkingRound8_of_exc (hF4 : GGNonsplitNbrMarkingTag .F4)
    (hE6 : GGNonsplitNbrMarkingTag .E6) (hE7 : GGNonsplitNbrMarkingTag .E7)
    (hE8 : GGNonsplitNbrMarkingTag .E8) (hTwE6 : GGNonsplitNbrMarkingTag .twistedE6) :
    GGNonsplitNbrMarkingRound8 :=
  ⟨ggNonsplitNbrMarkingTag_POmegaPlus, ggNonsplitNbrMarkingTag_POmegaMinus, hF4, hE6, hE7, hE8,
    hTwE6⟩

end Marking

end CFSG.StandardType
