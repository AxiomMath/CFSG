module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierTwoDCover
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierTwoDModel
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierTwoDAction

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType


theorem rckCarrierTwoD_holds : RCKCarrierTwoD := by
  intro τ p₀ S a hT p hp hp2 hTp i h hq hk _hQS
  let P := rckTwoD_canonicalData S hT hp hp2 hTp i hq hk
  obtain ⟨hstd, hfin, hperf, hsplit, hlong⟩ := rckTwoD_ggU_facts P.rank_four_le P.field_pos
  have hs1 := (rckTwoD_graph_labelled S hT i hk).2.1
  rw [RCKFrameCover, hs1, mul_one]
  refine ⟨ggU .POmegaMinus (compRank (componentRoots (rootCharHom a) i)) h, P.φ,
    rfl, hstd, P.range_eq, P.ker_le_center, hfin, hperf, hsplit, hlong, ?_⟩
  intro b hb
  exact rckTwoD_innerDiag_of_range S hT i hk _ P.φ P.range_eq hb

end CFSG.StandardType.RCKRP
