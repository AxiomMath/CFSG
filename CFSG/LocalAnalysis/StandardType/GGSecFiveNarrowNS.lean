module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNarrowNSDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePumpNbrSplit
public import CFSG.LocalAnalysis.StandardType.GGReflRealizedQFourNbrSplit

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

theorem ggSecFivePumpNbrInput_of_ns
    (h : GGSecFivePumpNbrNSInput) : GGSecFivePumpNbrInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit y K hnb
  by_cases hK : GGSplitLie p K
  · exact ggSecFivePumpNbrInput_split G p B Bs x L D J 𝒦 hcfg hsplit y K hnb hK
  · exact h G p B Bs x L D J 𝒦 hcfg hsplit y K hnb hK

theorem ggReflRealizedQFourNbrInput_of_ns
    (h : GGReflRealizedQFourNbrNSInput) : GGReflRealizedQFourNbrInput := by
  intro G _ _ B Bs x L D J 𝒦 hcfg hsplit y K hnb hKq
  by_cases hK : GGSplitLie 3 K
  · exact ggReflRealizedQFourNbrInput_split G B Bs x L D J 𝒦 hcfg hsplit y K hnb hK hKq
  · exact h G B Bs x L D J 𝒦 hcfg hsplit y K hnb hK hKq
end CFSG.StandardType

end
