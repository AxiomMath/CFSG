module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedFacts
import CFSG.ClassicalGroups.SpecialLinear.SLnThreeLocalCoords
import CFSG.ClassicalGroups.SpecialLinear.SLnThreeLocalRank
import CFSG.ClassicalGroups.SpecialLinear.SLnThreeLocalTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SignedFacts

open CFSG.ClassicalGroups.SLnThreeLocal
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.ModelTransport

theorem slK6cFacts_holds (n : ℕ) : SLK6cFacts n := by
  intro hn K _ _ hq
  exact ⟨c₀ K hn, c₀_signedCoords (three_ne_zero_of_natCard_mod_three hq) hn⟩

theorem slK6rFacts_holds (n : ℕ) : SLK6rFacts n := by
  intro hn K _ _ hq
  refine ⟨c₀ K hn, c₀_signedCoords (three_ne_zero_of_natCard_mod_three hq) hn, ?_⟩
  intro r hr hc _
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP K r := hc
  unfold ModelK6rRank
  exact ⟨⟨two_le_pRank_centralizer_c₀_weight_one hn,
      two_le_pRank_centralizer_c₀_weight_two hn,
      two_le_pRank_centralizer_c₀_weight_three hn⟩,
    one_le_pRank_centralizer_c₀_plane_a hn, one_le_pRank_centralizer_c₀_plane_b hn⟩

theorem slK7Facts_holds (n : ℕ) : SLK7Facts n := by
  intro hn K _ _ hq
  refine ⟨c₀ K hn, c₀_signedCoords (three_ne_zero_of_natCard_mod_three hq) hn, ?_, ?_⟩
  · intro ℓ hℓ _ hdvd
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    exact two_le_pRank_centralizer_range_of_dvd_add_one hq hn hdvd
  · intro ℓ hℓ _ hdvd
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    exact ⟨two_le_pRank_centralizer_range_of_dvd_sub_one hn hdvd,
      fun h7 => three_le_pRank_centralizer_range_of_dvd_sub_one hn h7 hdvd⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SignedFacts
