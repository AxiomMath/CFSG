module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteJoinDefs
public import CFSG.LocalAnalysis.StandardType.FS81.Reduction
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxOvergroupDefs

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly

@[expose] def GGFrameRouteJoinTBInputs : Prop :=
  FS81ThmACRankInput

@[expose] def GGFrameRouteJoinTBRestInputs : Prop :=
  FS81.FS81ThmACRankRest

end CFSG.StandardType.FrameRoute

end
