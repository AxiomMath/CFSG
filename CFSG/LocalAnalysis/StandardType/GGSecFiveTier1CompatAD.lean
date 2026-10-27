module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1LeviA
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1LeviD

public section

namespace CFSG.StandardType

section CompatAD

theorem ggSecFiveIdentCompatADInput_of_tier1 (hT : GGSecFiveTier1Input)
    (hC : GGSecFiveCompatLeviInput) : GGSecFiveIdentCompatADInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hAD
  have hADE : GGIsWeylMatrixAD M ∨ GGIsWeylMatrixE M := Or.inl hAD
  rcases hAD with ⟨n, e', hn, hM⟩ | ⟨n, e', hn, hM⟩
  · exact (ggSecFiveLeviA_of_tier1 hT hcfg hsplit hpres hn e' hM).compat hC hcfg hsplit hpres hADE
  · exact (ggSecFiveLeviD_of_tier1 hT hcfg hsplit hpres hn e' hM).compat hC hcfg hsplit hpres hADE

end CompatAD

end CFSG.StandardType

end
