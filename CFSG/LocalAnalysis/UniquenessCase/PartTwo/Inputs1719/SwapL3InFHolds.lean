module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SwapL3InF
import CFSG.LocalAnalysis.WeakClosure81.InFGroupSwapL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem k_SwapL3InF_holds : K_SwapL3InF := by
  intro Q _ _ L T n hF hsimple hL3 hn hT hLT hsw
  exact CFSG.LocalAnalysis.WeakClosure81.SwapL3.inF_top_of_swapsParabolics hF hsimple hL3 hn hT
    hLT hsw

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
