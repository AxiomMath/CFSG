module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesRestHalfMaxHolds
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6FiveHolds
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6ThreeSC

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly ExcFrames


@[expose] def GGSixBstarExcFramesRestResidualUntwisted : Prop :=
  ExcFramesHalf.BigElemAbelianToralBar .E7 3 ∧ ExcFramesHalf.BigElemAbelianToralBar .E7 5 ∧
    ExcFramesHalf.BigElemAbelianToralBar .E8 3 ∧ ExcFramesHalf.BigElemAbelianToralBar .E8 5 ∧
      GGSixBstarExcFrameOn .F4 GGExcE6NonsplitThreeLabel

theorem ggSixBstarExcFramesRestResidual_of_untwisted
    (h : GGSixBstarExcFramesRestResidualUntwisted) : GGSixBstarExcFramesRestResidual := by
  obtain ⟨h73, h75, h83, h85, hF3⟩ := h
  exact ⟨h73, h75, h83, h85, hF3,
    ggSixBstarExcFrameOn_TwE6NonsplitThree twistedE6ThreeSCUnique_holds
      twistedE6ThreeRefFrame_holds,
    ggSixBstarExcFrameOn_TwE6SplitFive twistedE6FiveSCUnique_holds twistedE6FiveRefFrame_holds⟩

end CFSG.StandardType
