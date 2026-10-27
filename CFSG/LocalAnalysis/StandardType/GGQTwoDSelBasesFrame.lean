module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDSelBases
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthChart

public section

namespace CFSG.StandardType.QTwo

section Frame

theorem ggQTwoDOrthBaseInputOn_holds {R : ℕ → Prop} : GGQTwoDOrthBaseInputOn R := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' _ hM hc
  obtain ⟨lab, hΛ, hhas, hn, htag⟩ := hc
  obtain ⟨Φ, hF, -, -, hZ, -⟩ :=
    qtwoOrthFrameCore_of_cfg hcfg (qtwo_label_le_three e' hM) hΛ hhas hn htag
  exact ⟨Φ, hF, hZ⟩

theorem ggQTwoLGenRankTwoInputOn_of_unitBase {R : ℕ → Prop} (hR : ∀ m, R m → 4 ≤ m)
    (hSM : GGQTwoDSelModuleInputOn R) (hU : GGQTwoDUnitBaseInputOn R) :
    GGQTwoLGenRankTwoInputOn R :=
  ggQTwoLGenRankTwoInputOn_of_bases hR hSM hU ggQTwoDOrthBaseInputOn_holds

end Frame

end CFSG.StandardType.QTwo

end
