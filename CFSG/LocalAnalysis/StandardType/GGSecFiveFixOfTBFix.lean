module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs

public section

namespace CFSG.StandardType

theorem ggSecFiveFixInput_of_tbFix
    (hT : GGTBFixInput) : GGSecFiveFixInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg _
  have hR := hcfg.1
  obtain ⟨y, K, hnbr⟩ := exists_ggNbr hR.1.1.2.2.2.2.2.2.2 hR.1.2.2
  exact hT G p B Bs x L D J hR.1 hR.2.1 hR.2.2.1 hR.2.2.2.1 y K hnbr (hcfg.2.1 y K hnbr)
    (Or.inr hcfg.2.1)

end CFSG.StandardType

end
