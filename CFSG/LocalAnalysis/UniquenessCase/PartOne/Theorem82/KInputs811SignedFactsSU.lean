module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedFacts
import CFSG.ClassicalGroups.Unitary.SUnThreeLocalCoords
import CFSG.ClassicalGroups.Unitary.SUnThreeLocalRank
import CFSG.ClassicalGroups.Unitary.SUnThreeLocalTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SignedFacts

open CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.SUnThreeLocal

theorem suK6cFacts_holds (n : ℕ) : SUK6cFacts n := by
  intro hn L _ _ σ q _ htr hσq hL hq
  obtain ⟨ζ⟩ := FixedCubeRoot.exists_of_card hq hL hσq
  exact ⟨c₀ ζ hn, c₀_signedCoords ζ htr hn⟩

theorem suK6rFacts_holds (n : ℕ) : SUK6rFacts n := by
  intro hn L _ _ σ q hσ htr hσq hL hq
  obtain ⟨ζ⟩ := FixedCubeRoot.exists_of_card hq hL hσq
  refine ⟨c₀ ζ hn, c₀_signedCoords ζ htr hn, ?_⟩
  intro r hr hChar _
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hChar
  exact ⟨⟨two_le_pRank_centralizer_c₀_weight_one hσ htr ζ hn,
      two_le_pRank_centralizer_c₀_weight_two hσ htr ζ hn,
      two_le_pRank_centralizer_c₀_weight_three hσ htr ζ hn⟩,
    one_le_pRank_centralizer_c₀_plane_a hσ htr ζ hn,
    one_le_pRank_centralizer_c₀_plane_b hσ htr ζ hn⟩

theorem suK7Facts_holds (n : ℕ) : SUK7Facts n := by
  intro hn L _ _ σ q hσ htr hσq hL hq
  obtain ⟨ζ⟩ := FixedCubeRoot.exists_of_card hq hL hσq
  refine ⟨c₀ ζ hn, c₀_signedCoords ζ htr hn, ?_, ?_⟩
  · intro ℓ hℓ _ hdvd
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    exact two_le_pRank_centralizer_range_of_dvd_sub_one hσ ζ hn hL hdvd
  · intro ℓ hℓ _ hdvd
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    exact ⟨two_le_pRank_centralizer_range_of_dvd_add_one hσ ζ hn hL hdvd,
      fun h7 => three_le_pRank_centralizer_range_of_dvd_add_one hσ ζ hn h7 hL hdvd⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SignedFacts
