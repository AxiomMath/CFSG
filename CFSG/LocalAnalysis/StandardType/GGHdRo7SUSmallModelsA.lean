module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallModelsAD13

public section

namespace CFSG.StandardType.HdRo7SU.Small

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem smModelsA_holds : SMModelsALeaf := by
  exact ⟨hdRo7SmAAux_case1, hdRo7SmAAux_case2, hdRo7SmAAux_case3, hdRo7SmAAux_case5,
    hdRo7SmAAux_case4⟩

end CFSG.StandardType.HdRo7SU.Small
