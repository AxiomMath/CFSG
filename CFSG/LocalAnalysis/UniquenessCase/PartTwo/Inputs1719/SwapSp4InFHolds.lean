module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SwapSp4InF
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupSwapSp4
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupSwapSp4Model
public import CFSG.LocalAnalysis.WeakClosure81.InFOneSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem k_SwapSp4InF_holds : K_SwapSp4InF := by
  intro Q _ _ L T n hF hsimple hSp hn hT hLT hsw
  obtain ⟨P₀, P₁, F, _, _, w, h⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.SwapSp4.exists_setting hF hsimple hSp hn hT hLT hsw
  exact F12.inF_top_of_inFFor hT h.inFFor

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
