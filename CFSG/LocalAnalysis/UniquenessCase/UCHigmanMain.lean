module

public import CFSG.LocalAnalysis.UniquenessCase.UCHigmanCore
public import CFSG.LocalAnalysis.UniquenessCase.UCK461

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

theorem higmanNatSL2_holds : HigmanNatSL2 := by
  intro G _ _ n hL V _ _ _ ρ _ hirr D hD hfix
  exact Higman.exists_natural_of_fixSub_eq_bot hL ρ hirr D hD hfix

end CFSG.LocalAnalysis.UniquenessCase.UCK
