module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLResidualsUni
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitTvSixQ2

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggLTransvectionCenterInputOn_of_not_unitDvd63All
    {S : ℕ → LargeEvenLabel → Prop}
    (h : GGLTransvectionCenterInputOn fun p lab => S p lab ∧ ¬ GGUnitDvd63Label p lab) :
    GGLTransvectionCenterInputOn S := by
  refine ggLTransvectionCenterInputOn_of_not_unitDvd63 ?_
  refine ggLTransvectionCenterInputOn_of_not_unitDvd63Two ?_
  intro G _ _ p B Bs x L D J hC hL
  refine h G p B Bs x L D J hC (hL.mono fun p lab hlab => ⟨hlab.1.1, fun hu => ?_⟩)
  by_cases hn : lab.n = 1
  · exact hlab.2 ⟨hu, hn⟩
  · exact hlab.1.2 ⟨hu, hn⟩

end CFSG.StandardType

