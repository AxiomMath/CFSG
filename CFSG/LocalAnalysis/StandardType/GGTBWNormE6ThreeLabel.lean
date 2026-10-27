module

public import CFSG.LocalAnalysis.StandardType.GGTBWNorm
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE6ThreeModel
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE6ThreeToral
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwoTorus

public section

namespace CFSG.StandardType.E6ThreeWNorm

open CFSG CFSG.Assembly TableBExc


theorem largeEvenLabelAll_wnormLift_E6_three {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .E6) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSCLift 3 R I := by
  have hn : 1 ≤ lab.n := hlab.1
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hn ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  refine ⟨K, i1, i2, hK, hQK, ?_⟩
  intro L' _ _ ψ hψ hker hperf A hA hAI h27 hsc hlift _ Λ _ _ M C V _ _ ι φ h α _ _ _ _ hgen s hs
  have h3n : ¬ 3 ∣ 2 ^ n := fun h => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rcases (by omega : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1) with h3 | h3
  · exact ggWNormConcl_five_recipe_E6 hn hK h3 ⟨hψ, hker, hperf, hA, hAI,
      hlift 5 (ggTorusLift_E6_three (by rw [hK]; exact h3)), h27, hsc⟩ ι φ h α hgen hs
  · exact ggWNormConcl_recipe_E6_three_plus (by rw [hK]; exact h3) ⟨hψ, hker, hperf, hA, hAI,
      hlift 4 E6Three.ggTorusLift_E6_two, h27, hsc⟩ ι φ h α hgen hs

end CFSG.StandardType.E6ThreeWNorm
