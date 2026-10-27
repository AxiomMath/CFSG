module

public import CFSG.LocalAnalysis.StandardType.GGK1ScExcPair
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs
import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Aut
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic

public section

namespace CFSG.StandardType.GGK0ExcCentreU

open CFSG CFSG.Assembly CFSG.StandardType

theorem pElement_inner_of_centred
    {lab : LargeEvenLabel} {p : ℕ} (hlab : LargeEvenInLambda2 lab) (hpair : GGKacExcPair lab p)
    (hc : GGKacCentred lab p) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ g ∈ I, g ^ p = 1 → g ∈ (MulAut.conj : R →* MulAut R).range := by
  intro Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  have hp : p.Prime := hpair.1
  rcases hpair.2.2.2 with h | h | h | h | h <;>
    (change tag = _ at h; subst tag)
  ·
    have hp3 : p ≠ 3 := fun h3 => hc ⟨Or.inl rfl, h3⟩
    dsimp only [LargeEvenLabelAll, LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
    obtain ⟨K, hField, hFinite, hK, hQ'⟩ := hQ
    letI : Field K := hField
    letI : Finite K := hFinite
    exact ⟨K, hField, hFinite, hK, hQ', TableBExc.ggOutdiagPrime_E6 hp hp3⟩
  ·
    have hp3 : p ≠ 3 := fun h3 => hc ⟨Or.inr rfl, h3⟩
    dsimp only [LargeEvenLabelAll, LargeEvenRawDatum, LargeEvenRecipeTwisted] at hQ ⊢
    obtain ⟨K, hField, hFinite, hK, hQ'⟩ := hQ
    letI : Field K := hField
    letI : Finite K := hFinite
    exact ⟨K, hField, hFinite, hK, hQ', TwE6Delta.ggOutdiagPrime_twE6 hlab.1 hK hp hp3⟩
  ·
    dsimp only [LargeEvenLabelAll, LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
    obtain ⟨K, hField, hFinite, hK, hQ'⟩ := hQ
    letI : Field K := hField
    letI : Finite K := hFinite
    haveI : CharP K 2 := charP_two_of_card hK
    exact ⟨K, hField, hFinite, hK, hQ',
      fun φ hφ _ => TableBExc.idImage_subset_inn_E7 K hφ⟩
  ·
    dsimp only [LargeEvenLabelAll, LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
    obtain ⟨K, hField, hFinite, hK, hQ'⟩ := hQ
    letI : Field K := hField
    letI : Finite K := hFinite
    haveI : CharP K 2 := charP_two_of_card hK
    exact ⟨K, hField, hFinite, hK, hQ',
      fun φ hφ _ => TableBExc.idImage_subset_inn_E8 K hφ⟩
  ·
    dsimp only [LargeEvenLabelAll, LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
    obtain ⟨K, hField, hFinite, hK, hQ'⟩ := hQ
    letI : Field K := hField
    letI : Finite K := hFinite
    haveI : CharP K 2 := charP_two_of_card hK
    exact ⟨K, hField, hFinite, hK, hQ',
      fun φ hφ _ => TableBF4.idImage_subset_inn K hφ⟩

end CFSG.StandardType.GGK0ExcCentreU

end
