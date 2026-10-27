module

public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneLinearLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneOmegaLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneUnitaryLabel

public section

namespace CFSG.StandardType


theorem ggNbrFrameInputOne_holds : GGNbrFrameInputOne := by
  intro p hp hp2 lab hlab hfl
  rcases hfl with h | h | h
  · exact largeEvenLabelAll_frame_omegaMinus hp hp2 hlab h
  · exact largeEvenLabelAll_frame_linear hp hp2 hlab h
  · exact largeEvenLabelAll_frame_unitary hp hp2 hlab h

end CFSG.StandardType

end
