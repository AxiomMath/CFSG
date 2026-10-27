module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallClass6
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallClass7

public section

namespace CFSG.StandardType.HdRo7D.Small

theorem dSmClass_holds : DSmClassLeaf := fun hT =>
  ⟨(dSmClass6 hT).1, (dSmClass6 hT).2, (dSmClass7 hT).1, (dSmClass7 hT).2⟩

end CFSG.StandardType.HdRo7D.Small
