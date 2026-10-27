module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1CitedDefs
public import Certificates.Certificate2264
public import Certificates.Certificate2267
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosHolds
import CFSG.LocalAnalysis.StandardType.GGStdPosLocalConj

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

theorem ggSecFiveKGCentInput_of_tags
    (hJR : GGSecFiveJReflInput)
    (hA : GGKGCentTagStmt .PSL) (hD : GGKGCentTagStmt .POmegaPlus)
    (hE6 : GGKGCentTagStmt .E6) (hE7 : GGKGCentTagStmt .E7) (hE8 : GGKGCentTagStmt .E8) :
    GGSecFiveKGCentInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsL X hX hsplit
  have hr := hJR G p B Bs x L D J 𝒦 hcfg hsL
  obtain ⟨tg, n, f, ψ, hloc⟩ := ggKGPosRankStmt_holds G p B Bs x L D J 𝒦 hcfg X hX hsplit
  obtain ⟨k, hstd⟩ := ggKGPos_exists_stdPos hloc
  have hloc' := ggKGPosLocalHyp_comp_conj hloc k
  rcases hloc.2.1.2.2.1 with rfl | rfl | rfl | rfl | rfl
  · exact hA G p B Bs x L D J 𝒦 hcfg hsL hr X hX n f _ hloc' hstd
  · exact hD G p B Bs x L D J 𝒦 hcfg hsL hr X hX n f _ hloc' hstd
  · exact hE6 G p B Bs x L D J 𝒦 hcfg hsL hr X hX n f _ hloc' hstd
  · exact hE7 G p B Bs x L D J 𝒦 hcfg hsL hr X hX n f _ hloc' hstd
  · exact hE8 G p B Bs x L D J 𝒦 hcfg hsL hr X hX n f _ hloc' hstd

end CFSG.StandardType

end
