module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthChart
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitL1Chart

public section

namespace CFSG.StandardType.QTwo


theorem ggQTwoDL1ChartLInput_of_cells (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hFrame : GGQTwoFrameInput) : GGQTwoDL1ChartLInput := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM
  by_cases hL : qtwoOrthL G L 𝒦
  · obtain ⟨Φ, hF, h5, hZ⟩ := qtwoDL1Chart_orth_L hFrame hcfg m e' hm hM hL
    exact Or.inr ⟨Φ, hF, h5, hZ⟩
  · exact ggQTwoDUnit_chartL ggLabelRigidInput_holds hTBF hWI hcfg e' hm hM hL

end CFSG.StandardType.QTwo

end
