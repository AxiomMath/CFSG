module

public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsExc
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6Nonsplit
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE8Rest
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxElem
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxToral
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfTwoLocal
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesResidualLabels
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTagsE6
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6Nonsplit
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6Split

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly ExcFrames

section Holds

@[expose] def GGSixBstarExcFramesRestResidual : Prop :=
  ExcFramesHalf.BigElemAbelianToralBar .E7 3 ∧ ExcFramesHalf.BigElemAbelianToralBar .E7 5 ∧
    ExcFramesHalf.BigElemAbelianToralBar .E8 3 ∧ ExcFramesHalf.BigElemAbelianToralBar .E8 5 ∧
      GGSixBstarExcFrameOn .F4 GGExcE6NonsplitThreeLabel ∧
        GGSixBstarExcFrameOn .F4 GGExcTwE6NonsplitThreeLabel ∧
          GGSixBstarExcFrameOn .E6 GGExcTwE6SplitFiveLabel

theorem ggSixBstarExcFramesRestHalfMax_of_residual (h : GGSixBstarExcFramesRestResidual) :
    GGSixBstarExcFramesRestHalfMax := by
  obtain ⟨h73, h75, h83, h85, hF3, hT3, hT5⟩ := h
  exact ⟨ggExcNonsplitRankInput_F4, ExcFramesHalf.ggExcHalfMaxElemInput_E7 h73 h75,
    ggExcNonsplitRankInput_E7, ExcFramesHalf.ggExcHalfMaxElemInput_E8 h83 h85,
    ggSixBstarExcFrameOn_E8Rest, ggSixBstarExcFrameOn_E6Split,
    ggSixBstarExcFrameOn_E6Nonsplit_of_three hF3, ggSixBstarExcFrameOn_TwE6Split_of_five hT5,
    ggSixBstarExcFrameOn_TwE6Nonsplit_of_three hT3⟩

end Holds

end CFSG.StandardType
