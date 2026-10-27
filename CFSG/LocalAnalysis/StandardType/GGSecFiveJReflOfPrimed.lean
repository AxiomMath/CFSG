module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1CitedDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJReflOfCore

public section

namespace CFSG.StandardType

theorem ggSecFiveJReflInput_of_primed
    (h : GGSecFiveJReflInput') : GGSecFiveJReflInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hL
  exact h G p B Bs x L D J 𝒦 (ggSecFiveRouteCfg'_of_routeCfg hcfg) hL

end CFSG.StandardType

end
