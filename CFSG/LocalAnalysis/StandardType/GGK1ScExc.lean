module

public import CFSG.LocalAnalysis.StandardType.GGKacK0
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE6
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE7
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaCenter

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem largeEvenLabelAll_centerPrime_exc
    {lab : LargeEvenLabel} {p : ℕ} (hlab : LargeEvenInLambda2 lab) (hgen : GGKacGeneric lab p) :
    LargeEvenLabelAll lab fun R _ _ _ => GGCenterPrime p R := by
  intro Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  have hp : p.Prime := hgen.1
  have hp2 : p ≠ 2 := hgen.2.1
  rcases hgen.2.2.2.1 with h | h | h | h | h <;>
    (change tag = _ at h; subst tag)
  ·
    have hp3 : p ≠ 3 := by
      intro h3
      exact hgen.2.2.2.2.2.1 ⟨Or.inl rfl, Or.inl h3⟩
    dsimp only [LargeEvenLabelAll, LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
    obtain ⟨K, hField, hFinite, hK, hQ'⟩ := hQ
    letI : Field K := hField
    letI : Finite K := hFinite
    haveI : CharP K 2 := charP_two_of_card hK
    exact ⟨K, hField, hFinite, hK, hQ', ExcSplitL.ggCenterPrime_recipe_E6 hp hp2 hp3⟩
  ·
    have hp3 : p ≠ 3 := by
      intro h3
      exact hgen.2.2.2.2.2.1 ⟨Or.inr rfl, Or.inl h3⟩
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

end CFSG.StandardType

end
