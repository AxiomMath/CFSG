module

public import CFSG.Quasithin.H13.NQBlockCharNormalizerConfine
public import CFSG.Quasithin.H13.NQCatPrimeLinearThreeAmbient

public section

namespace CFSG.Quasithin.H13.NQBlock

theorem primeLinearThreeAmbientPlane_of
    (hI : ∀ (F : Type) [Field F] [Finite F], NQCat.OddLinearThreeInvolutionSylowStructure F) :
    PrimeLinearThreeAmbientPlane := by
  intro F _ _ K _ _ q _ hFq hq5 D _ hD α S A hA hAq p _ hp2 X hXA hXn hX2 hXp hXr
  obtain ⟨hpq, V, hV, -, -, hX, -⟩ :=
    NQCat.prime_linear_three_ambient_model_identifies_original_witness_with_actual_unipotent_plane
      (hI F) hFq hq5 D hD α S hA hAq hp2 hXA hXn hX2 hXp hXr
  exact ⟨hpq, V, hV, hX⟩

theorem primeLinearThreeAmbientPrime_of
    (hI : ∀ (F : Type) [Field F] [Finite F], NQCat.OddLinearThreeInvolutionSylowStructure F) :
    PrimeLinearThreeAmbientPrime :=
  fun F _ _ K _ _ q _ hFq hq5 D _ hD α S A hA hAq p _ hp2 X hXA hXn hX2 hXp hXr =>
    (primeLinearThreeAmbientPlane_of hI F K q hFq hq5 D hD α S A hA hAq p hp2 X hXA hXn hX2 hXp
      hXr).1

end CFSG.Quasithin.H13.NQBlock
