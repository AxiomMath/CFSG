module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K339Z
public import CFSG.LocalAnalysis.UniquenessCase.UC22Seed

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

theorem seedBridge_iff_k339SeedBridge : SeedBridge ↔ K339SeedBridge :=
  Iff.rfl

theorem k339Z_of_k339SeedBridge (hK1 : K339SeedBridge) : K339Z :=
  k339Z_of_seedBridge (seedBridge_iff_k339SeedBridge.mpr hK1)

end CFSG.LocalAnalysis.UniquenessCase.UC22
