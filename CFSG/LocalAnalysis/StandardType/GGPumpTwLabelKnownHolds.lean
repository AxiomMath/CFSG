module

public import CFSG.LocalAnalysis.StandardType.GGPumpTwLabLaneAU
public import CFSG.LocalAnalysis.StandardType.GGPumpTwLabLaneCD
public import CFSG.LocalAnalysis.StandardType.GGPumpTwLabLaneExc
public import CFSG.LocalAnalysis.StandardType.GGPumpTwLabLaneSmall
public import CFSG.LocalAnalysis.StandardType.GGPumpTwLabCover
public import CFSG.LocalAnalysis.StandardType.GGR4PumpTwKnownDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggPumpTwLabelKnown_holds
    (hB2 : GGK0ExcB2) : GGPumpTwLabelKnown := by
  intro lab hlab
  rcases ggPumpTwLab_cover lab hlab with h | h | h | h | h
  · exact ggPumpTwLab_laneAU lab hlab h
  · exact ggPumpTwLab_laneCD lab hlab h
  · exact ggPumpTwLabRAKnown_holds lab hlab h
  · exact ggPumpTwLab_laneExc hB2 lab hlab h
  · exact ggPumpTwLab_laneSmall lab hlab h

end CFSG.StandardType

end
