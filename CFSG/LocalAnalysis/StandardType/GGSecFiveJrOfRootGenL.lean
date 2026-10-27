module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMPrimeInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggSecFiveJrInput_of_rootGenL
    (hRootGenL : GGSecFiveRootGenLInput) : GGSecFiveJrInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit r hr hrefl
  have hconf : GGConfig p B Bs x L D J := hcfg.1.1
  have hstdpre : LargeEvenStdSubPre p B x L D J := hconf.2.2.1
  have hJL : J ≤ L := hstdpre.2.2.2.2.2.1.1.trans inf_le_left
  obtain ⟨g, hg, hgN, hgφ⟩ := mem_ggAutomizer_iff.mp hr
  exact hRootGenL G p B Bs x L D J 𝒦 hcfg hsplit r
    (mem_ggAutomizer_iff.mpr ⟨g, hJL hg, hgN, hgφ⟩) hrefl

end CFSG.StandardType

end
