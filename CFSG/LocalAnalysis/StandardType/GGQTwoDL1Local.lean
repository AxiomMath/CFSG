module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1Chart
public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1Edge
public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1LocalU
public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1LocalO

public section

namespace CFSG.StandardType.QTwo

section Inputs


theorem ggQTwoDL1EdgeLocalInput_of_charts (hCh : GGQTwoDL1ChartInput) (hW : QTwoDL1OrthPair) :
    GGQTwoDL1EdgeLocalInput := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM X hX r hrA hrC r' hr'A hr'C hne
  have hrefl := ggCoxRefl_isReflection hcfg.2.2.2.1.2 hrC
  have hrefl' := ggCoxRefl_isReflection hcfg.2.2.2.1.2 hr'C
  rcases hCh G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM X hX with
    ⟨K, _, _, _, n, ψ, hK, h, hrange, hd, -⟩ | ⟨Φ, hF, -, hZ⟩
  · exact qtwoDL1_local_unit hK h hrange hd hrA hr'A hrefl hrefl' hne
  · exact qtwoDL1_local_orth hW Φ hF hZ hrA hr'A hrefl hrefl' hne

end Inputs

end CFSG.StandardType.QTwo

end
