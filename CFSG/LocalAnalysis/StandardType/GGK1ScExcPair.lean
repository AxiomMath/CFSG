module

public import CFSG.LocalAnalysis.StandardType.GGK1ScExc
public import CFSG.LocalAnalysis.StandardType.GGK0ExcB3

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem largeEvenLabelAll_centerPrime_excPair
    {lab : LargeEvenLabel} {p : ℕ} (hlab : LargeEvenInLambda2 lab) (hpair : GGKacExcPair lab p)
    (hc : GGKacCentred lab p) :
    LargeEvenLabelAll lab fun R _ _ _ => GGCenterPrime p R := by
  intro Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  have hp : p.Prime := hpair.1
  have hp2 : p ≠ 2 := hpair.2.1
  rcases hpair.2.2.2 with h | h | h | h | h <;>
    (change tag = _ at h; subst tag)
  ·
    have hp3 : p ≠ 3 := fun h3 => hc ⟨Or.inl rfl, h3⟩
    dsimp only [LargeEvenLabelAll, LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
    obtain ⟨K, hField, hFinite, hK, hQ'⟩ := hQ
    letI : Field K := hField
    letI : Finite K := hFinite
    haveI : CharP K 2 := charP_two_of_card hK
    exact ⟨K, hField, hFinite, hK, hQ', ExcSplitL.ggCenterPrime_recipe_E6 hp hp2 hp3⟩
  ·
    have hp3 : p ≠ 3 := fun h3 => hc ⟨Or.inr rfl, h3⟩
    dsimp only [LargeEvenLabelAll, LargeEvenRawDatum, LargeEvenRecipeTwisted] at hQ ⊢
    obtain ⟨K, hField, hFinite, hK, hQ'⟩ := hQ
    letI : Field K := hField
    letI : Finite K := hFinite
    exact ⟨K, hField, hFinite, hK, hQ',
      TwE6Delta.ggCenterPrime_twE6 hlab.1 hK hp hp2 hp3⟩
  ·
    dsimp only [LargeEvenLabelAll, LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
    obtain ⟨K, hField, hFinite, hK, hQ'⟩ := hQ
    letI : Field K := hField
    letI : Finite K := hFinite
    haveI : CharP K 2 := charP_two_of_card hK
    exact ⟨K, hField, hFinite, hK, hQ',
      ExcSplitL.ggCenterPrime_recipe_E7 hlab.1 hK hp hp2⟩
  ·
    dsimp only [LargeEvenLabelAll, LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
    obtain ⟨K, hField, hFinite, hK, hQ'⟩ := hQ
    letI : Field K := hField
    letI : Finite K := hFinite
    haveI : CharP K 2 := charP_two_of_card hK
    exact ⟨K, hField, hFinite, hK, hQ', ExcSplitL.ggCenterPrime_recipe_E8 hp hp2⟩
  ·
    dsimp only [LargeEvenLabelAll, LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
    obtain ⟨K, hField, hFinite, hK, hQ'⟩ := hQ
    letI : Field K := hField
    letI : Finite K := hFinite
    haveI : CharP K 2 := charP_two_of_card hK
    exact ⟨K, hField, hFinite, hK, hQ', ExcSplitL.ggCenterPrime_recipe_F4 hp hp2⟩

theorem ggK0Schur_excPair :
    GGK0Schur fun lab p => GGKacExcPair lab p ∧ GGKacCentred lab p := by
  intro p lab hlab hgen
  refine (largeEvenLabelAll_centerPrime_excPair hlab hgen.1 hgen.2).mono fun R _ I F hR => ?_
  intro L' _ _ ψ hψ hker hperf
  exact ((Nat.Prime.coprime_iff_not_dvd hgen.1.1).mpr (hR L' ψ hψ hker hperf)).symm

end CFSG.StandardType

end
