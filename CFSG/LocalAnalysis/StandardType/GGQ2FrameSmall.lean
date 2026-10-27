module

public import CFSG.LocalAnalysis.StandardType.GGQ2FrameSplit
public import CFSG.LocalAnalysis.StandardType.GGQ2ExtCoverSmall

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly

theorem placementInputOn_small
    (catalogue : FrameKind → RawFrameData) :
    PlacementInputOn SmallLabel catalogue := by
  intro G _ _ p B Bs x L D J hS hp hm
  subst hp
  exact (ggG0_not_marking_small hS.1 hm).elim

theorem placementCoreInputOn_small
    (catalogue : FrameKind → RawFrameData) :
    PlacementCoreInputOn SmallLabel catalogue := by
  intro G _ _ p B Bs x L D J hS hp hm
  subst hp
  exact (ggG0_not_marking_small hS.1 hm).elim

end CFSG.StandardType.GGQ2Frame

end
