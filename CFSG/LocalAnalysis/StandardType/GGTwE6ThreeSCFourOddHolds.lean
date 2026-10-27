module

public import CFSG.LocalAnalysis.StandardType.GGTwE6R4Defs
public import CFSG.LocalAnalysis.StandardType.GGTwE6R4Index
public import CFSG.LocalAnalysis.StandardType.GGTwE6R4RankSix
public import CFSG.LocalAnalysis.StandardType.GGTwE6R4Count
public import CFSG.LocalAnalysis.StandardType.GGTwE6R4CoverNine
public import CFSG.LocalAnalysis.StandardType.GGTwE6R4CoverThree
public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.StandardType.NoOffTwE6Three


theorem ggTwE6ThreeSCFourNotTwoLocalOddInput_of_kga1 (h82 : GGTwE6ThreeTwoLocalInnToralInput)
    (h84 : GGTwE6ThreeToralTypeMinusOneInput) (h5 : GGTwE6ThreeNoRankSixInput) :
    GGTwE6ThreeSCFourNotTwoLocalOddInput := by
  intro K _ _ n hn hK h3
  haveI := TwE6Delta.finite_recipeR hK
  obtain ⟨σ, _, ε, hε⟩ := TwE6Transport.exists_recipeConj (K := K) hn hK
  have hI : TwE6Delta.RecipeI K n = ((TwE6Transport.recipeConj σ ε).range : Set _) :=
    Set.ext fun φ => (hε φ).symm
  rw [hI]
  refine TwE6R4.oddNotTwoLocal_of_torus (TwE6Delta.center_recipeR_eq_bot hn hK)
    (TwE6Transport.recipeConj σ ε).range ?_ ?_ ?_
  · intro S hSJ hS h4 hV
    obtain ⟨V, hV0, hV2, hSV⟩ := hV
    obtain ⟨Y, hSY, hYI, hY, hY6⟩ := TwE6R4.exists_rankSix_recipe h82 h84 hn hK h3 hS
      (fun φ hφ => (hε φ).1 (hSJ hφ)) h4 hV0 hV2 hSV
    exact ⟨Y, hSY, fun φ hφ => (hε φ).2 (hYI φ hφ), hY, hY6⟩
  · intro Y hYJ hY hY6
    exact TwE6R4.three_pow_five_le_inf_conj hn hK (fun φ hφ => (hε φ).1 (hYJ hφ)) hY6
  · intro L' _ _ ψ hψ hker hperf hodd
    refine ⟨TwE6R4.card_ker_dvd_three hn hK hψ hker hperf hodd, fun Y hYJ hY hY6 => ?_⟩
    have hYI : ∀ φ ∈ Y, φ ∈ TwE6Delta.RecipeI K n := fun φ hφ => (hε φ).1 (hYJ hφ)
    by_cases h9 : 9 ∣ 2 ^ n + 1
    · obtain ⟨hc, hinn⟩ := TwE6R4.cover_commute_of_nine hn hK h9 hψ hker hperf hYI hY hY6
      exact ⟨hc, Or.inl hinn⟩
    · obtain ⟨hc, hcube⟩ :=
        TwE6R4.cover_commute_of_not_nine h5 hn hK h3 h9 hψ hker hperf hodd hYI hY hY6
      exact ⟨hc, Or.inr hcube⟩

end CFSG.StandardType

