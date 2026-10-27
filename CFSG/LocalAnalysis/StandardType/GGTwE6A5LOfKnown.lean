module

public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCoverSetting
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLSmall
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLTorusBridge
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLParity
import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three
import CFSG.LocalAnalysis.StandardType.GGTableB

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint TableB

theorem ggTwE6A5LKnownAd_of_families (hT : GGTitsThreeCentInput)
    (hTC : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag ≠ .E6 → lab.tag ≠ .E7 →
      lab.tag ≠ .E8 → lab.tag ≠ .F4 → lab.tag ≠ .twE6 → lab.tag ≠ .twF4 → lab.tag ≠ .twF4der →
      lab.tag ≠ .twB2 → lab.tag ≠ .B2der → lab.tag ≠ .G2der →
      (GGNoThreeCenter lab ∨ lab.rank + 1 ≤ 6) → GGTwE6A5LAt lab)
    (hE6 : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → (lab.tag = .E6 ∨ lab.tag = .twE6) →
      GGNoThreeCenter lab → GGTwE6A5LAt lab)
    (hF4 : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → (lab.tag = .F4 ∨ lab.tag = .twF4) →
      GGTwE6A5LAt lab) :
    GGTwE6A5LKnownAd := by
  intro lab hlab
  change GGTwE6A5LAt lab
  obtain ⟨tag, r, g⟩ := lab
  cases tag
  case twB2 => exact ggTwE6A5LAt_small hT hlab (Or.inl rfl)
  case B2der => exact ggTwE6A5LAt_small hT hlab (Or.inr (Or.inl rfl))
  case G2der => exact ggTwE6A5LAt_small hT hlab (Or.inr (Or.inr (Or.inl rfl)))
  case twF4der => exact ggTwE6A5LAt_small hT hlab (Or.inr (Or.inr (Or.inr rfl)))
  case E7 =>
    rcases three_dvd_two_pow_add_one_or_sub_one g with h | h
    · exact ggTwE6A5LAt_of_torusLift
        (largeEvenLabelAll_torusLift_excPlus_threeFive (Or.inl rfl) h)
    · exact ggTwE6A5LAt_of_torusLift
        (largeEvenLabelAll_torusLift_excMinus_threeFive (Or.inl rfl) h)
  case E8 =>
    rcases three_dvd_two_pow_add_one_or_sub_one g with h | h
    · exact ggTwE6A5LAt_of_torusLift
        (largeEvenLabelAll_torusLift_excPlus_threeFive (Or.inr rfl) h)
    · exact ggTwE6A5LAt_of_torusLift
        (largeEvenLabelAll_torusLift_excMinus_threeFive (Or.inr rfl) h)
  case F4 => exact hF4 _ hlab (Or.inl rfl)
  case twF4 => exact hF4 _ hlab (Or.inr rfl)
  case twE6 =>
    by_cases h : 3 ∣ 2 ^ g + 1
    · exact ggTwE6A5LAt_twE6 rfl h
    · exact hE6 _ hlab (Or.inr rfl) h
  case E6 =>
    by_cases h : 3 ∣ 2 ^ g - 1
    · exact ggTwE6A5LAt_of_torusLift (largeEvenLabelAll_torusLift_E6_three rfl h)
    · exact hE6 _ hlab (Or.inl rfl) h
  case A =>
    by_cases h : 3 ∣ r + 1 ∧ 3 ∣ 2 ^ g - 1
    · by_cases hr : r + 1 ≤ 6
      · exact hTC _ hlab (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
          (by simp) (by simp) (by simp) (Or.inr hr)
      · exact ggTwE6A5LAt_of_torusLift
          (largeEvenLabelAll_torusLift_typeA_threeFive rfl h.2 (by dsimp only; omega))
    · exact hTC _ hlab (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        (by simp) (by simp) (by simp) (Or.inl h)
  case twA =>
    by_cases h : 3 ∣ r + 1 ∧ 3 ∣ 2 ^ g + 1
    · by_cases hr : r + 1 ≤ 6
      · exact hTC _ hlab (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
          (by simp) (by simp) (by simp) (Or.inr hr)
      · exact ggTwE6A5LAt_of_torusLift
          (largeEvenLabelAll_torusLift_twA_threeFive hlab rfl h.2 (by dsimp only; omega))
    · exact hTC _ hlab (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        (by simp) (by simp) (by simp) (Or.inl h)
  all_goals
    exact hTC _ hlab (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (Or.inl trivial)

end CFSG.StandardType.SCFourCover

end
