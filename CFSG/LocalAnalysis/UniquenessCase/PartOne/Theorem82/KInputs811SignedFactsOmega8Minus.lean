module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedFacts
import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalCoords
import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalRankR
import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalRankRHeis
import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalRankP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SignedFacts

open CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal
  (c₀ c₀_signedCoords two_le_pRank_centralizer_c₀_point two_le_pRank_centralizer_c₀_pair
   two_le_pRank_centralizer_c₀_u one_le_pRank_centralizer_c₀_u_e₂
   two_le_pRank_centralizer_c₀_range)

theorem omega8MinusK6cFacts_holds : Omega8MinusK6cFacts := by
  intro K _ _ h3 b c hbc
  exact ⟨c₀ h3 hbc, c₀_signedCoords h3 hbc⟩

theorem omega8MinusK6rFacts_holds : Omega8MinusK6rFacts := by
  intro K _ _ h3 b c hbc
  refine ⟨c₀ h3 hbc, c₀_signedCoords h3 hbc, ?_⟩
  intro r hr hc h5
  haveI : CharP K r := hc
  have hr2 : r ≠ 2 := by omega
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact two_le_pRank_centralizer_c₀_point h3 hbc hr (Multiplicative.ofAdd ![1, 0, 0]) rfl
  · exact two_le_pRank_centralizer_c₀_point h3 hbc hr (Multiplicative.ofAdd ![1, 1, 0]) rfl
  · exact two_le_pRank_centralizer_c₀_u h3 hbc hr hr2
  · exact le_trans (by norm_num : 1 ≤ 2) (two_le_pRank_centralizer_c₀_pair h3 hbc hr
      (Multiplicative.ofAdd ![1, 0, 0]) (Multiplicative.ofAdd ![0, 1, 0]) rfl rfl)
  · exact one_le_pRank_centralizer_c₀_u_e₂ h3 hbc hr hr2

theorem omega8MinusK7Facts_holds : Omega8MinusK7Facts := by
  intro K _ _ h3 b c hbc
  refine ⟨c₀ h3 hbc, c₀_signedCoords h3 hbc, ?_⟩
  intro ℓ hℓ h5 hdvd
  have hℓ2 : ℓ ≠ 2 := by omega
  exact two_le_pRank_centralizer_c₀_range h3 hbc hℓ hℓ2 hdvd

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SignedFacts
