module

public import CFSG.RankThree.PartOne.KFOUT3.KtyRow3
public import CFSG.RankThree.PartOne.KLAY.RootLayerRow3

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KLAY

theorem kf1322KtyRow3_holds :
    KF1322KtyRow 3 := by
  refine kf1322KtyRow3_of_layers ?_
  intro p f K _ σ hP
  exact ⟨fun v hv1 hv => rootLayer_row3_s0 hP v hv1 hv,
    fun v hv1 hv => rootLayer_row3_s1 hP v hv1 hv⟩

end CFSG.RankThree.PartOne.KFOUT3
