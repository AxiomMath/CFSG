module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedFacts
import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalCoords
import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalFrameExists
import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalK6rWeightOne
import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalK6rWeightTwo
import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalK6rWeightThree
import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalK7Pts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SignedFacts

open CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.ModelTransport (ModelK6rRank ModelK7Dvd)

private theorem ringChar_ne_two {K : Type} [Field K] (h2 : (2 : K) ≠ 0) : ringChar K ≠ 2 := by
  intro h
  haveI : CharP K 2 := ringChar.of_eq h
  exact h2 (CharP.cast_eq_zero K 2)

theorem omega7K6cFacts_holds : Omega7K6cFacts := by
  intro K _ _ h2 h3
  obtain ⟨F⟩ := Frame.nonempty (ringChar_ne_two h2) h3
  exact ⟨c₀ F, c₀_signedCoords F⟩

theorem omega7K6rFacts_holds : Omega7K6rFacts := by
  intro K _ _ h2 h3
  obtain ⟨F⟩ := Frame.nonempty (ringChar_ne_two h2) h3
  refine ⟨c₀ F, c₀_signedCoords F, ?_⟩
  intro r _ hchar _
  haveI : CharP K r := hchar
  have hrc : ringChar K = r := ringChar.eq K r
  unfold ModelK6rRank
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [← hrc]; exact two_le_pRank_centralizer_c₀_weight_one F
  · rw [← hrc]; exact two_le_pRank_centralizer_c₀_weight_two F
  · rw [← hrc]; exact two_le_pRank_centralizer_c₀_weight_three F
  · rw [← hrc]; exact one_le_pRank_centralizer_c₀_pair_e₀_e₁ F
  · rw [← hrc]; exact one_le_pRank_centralizer_c₀_pair_u_e₂ F

theorem omega7K7Facts_holds : Omega7K7Facts := by
  intro K _ _ h2 h3
  obtain ⟨F⟩ := Frame.nonempty (ringChar_ne_two h2) h3
  refine ⟨c₀ F, c₀_signedCoords F, ?_, ?_⟩
  · intro ℓ hℓ h5 hdvd
    exact two_le_pRank_centralizer_range F hℓ (by omega) hdvd
  · intro ℓ hℓ h5 hdvd
    unfold ModelK7Dvd
    exact k7_b_omega7 F hℓ (by omega) hdvd

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SignedFacts
