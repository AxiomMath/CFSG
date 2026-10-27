module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1TypeA
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1TypeD

public section

namespace CFSG.StandardType

section Tier1

theorem ggSecFiveIdentADInput_of_tier1 (hT : GGSecFiveTier1Input) : GGSecFiveIdentADInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hAD
  rcases hAD with ⟨n, e', hn, hM⟩ | ⟨n, e', hn, hM⟩
  · exact ggSecFiveIdentA_of_tier1 hT hcfg hsplit hpres hn e' hM
  · exact ggSecFiveIdentD_of_tier1 hT hcfg hsplit hpres hn e' hM

end Tier1

end CFSG.StandardType

end
