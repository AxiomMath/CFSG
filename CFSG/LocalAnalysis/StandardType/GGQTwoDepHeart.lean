module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDepFive
public import CFSG.LocalAnalysis.StandardType.GGWAutHeart

public section

namespace CFSG.StandardType

theorem ggQ2_heartInput_of_omega (hK : GGReflClassOmegaInput) : GGQ2HeartInput := by
  intro D _ e hE6 hdim A hW hTF
  exact ggWAut_heartE6 (ggWAut_engine hK) hK D e hE6 hdim A hW hTF

end CFSG.StandardType

end
