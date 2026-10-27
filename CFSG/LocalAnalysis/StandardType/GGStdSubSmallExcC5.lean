module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcSplit
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeSmall
public import CFSG.LocalAnalysis.StandardType.GGIOneExcFacts
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6TwoThree
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6

public section

namespace CFSG.StandardType.SmallExc

open CFSG.Assembly

@[expose] def GGE6TwoNormSmallInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    GGStdSubTwoTorusNormSmall 3 4 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K)

@[expose] def GGE7TwoNormSmallInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    GGStdSubTwoTorusNormSmall 3 6 (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K)

@[expose] def GGE8TwoNormSmallInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    GGStdSubTwoTorusNormSmall 3 7 (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K)

@[expose] def GGF4TwoNormSmallInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    GGStdSubTwoTorusNormSmall 3 3 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K)

section Certs


theorem largeEvenLabelAll_normSmall_excTwoThree (h6 : GGE6TwoNormSmallInput)
    (h7 : GGE7TwoNormSmallInput) (h8 : GGE8TwoNormSmallInput) (hF4 : GGF4TwoNormSmallInput)
    {p : ℕ} {lab : LargeEvenLabel} (h : ExcTwoThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧ ∃ r, GGTorusLift p r R ∧
      GGStdSubTwoTorusNormSmall p r R I ∧ GGStdSubTwoTorusDeltaSmall p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hn, rfl⟩ := h
  dsimp only at htag hn
  subst hn
  intro Q hQ
  have hC := ggExcTwoCenterThreeInput_holds
  rcases htag with rfl | rfl | rfl | rfl <;> dsimp only [LargeEvenRawDatum] at hQ ⊢ <;>
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  all_goals
    have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
    have : CharP K 2 := charP_two_of_card hK
  · have hO : GGOutdiagPrime 3 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) :=
      fun φ hφ _ => TableBExc.E6Three.recipeID_subset_inn_E6_two hK2 hφ
    exact ⟨K, i1, i2, hK, hq, ggOutdiagOdd_of_prime hO, 4,
      TableBExc.E6Three.ggTorusLift_E6_two (K := K), h6 K hK2,
      ggStdSubTwoTorusDeltaSmall_of_delta
        (ggStdSubTwoTorusDelta_of_prime hO (ggCenterPrime_recipe_E6_two hK2 Nat.prime_three))⟩
  · exact ⟨K, i1, i2, hK, hq, ggOutdiagOdd_of_prime (ggIE_outdiagPrime_E7Two (K := K)), 6,
      TableBExcTwo.ggTorusLift_E7Two, h7 K hK2,
      ggStdSubTwoTorusDeltaSmall_of_delta
        (ggStdSubTwoTorusDelta_of_prime (ggIE_outdiagPrime_E7Two (K := K)) (hC.1 K hK2))⟩
  · exact ⟨K, i1, i2, hK, hq, ggOutdiagOdd_of_prime (ggIE_outdiagPrime_E8Two (K := K)), 7,
      TableBExcTwo.ggTorusLift_E8Two, h8 K hK2,
      ggStdSubTwoTorusDeltaSmall_of_delta
        (ggStdSubTwoTorusDelta_of_prime (ggIE_outdiagPrime_E8Two (K := K)) (hC.2.1 K hK2))⟩
  · exact ⟨K, i1, i2, hK, hq, ggOutdiagOdd_of_prime (ggIE_outdiagPrime_F4Two (K := K)), 3,
      TableBF4Two.ggTorusLift_F4Two, hF4 K hK2,
      ggStdSubTwoTorusDeltaSmall_of_delta
        (ggStdSubTwoTorusDelta_of_prime (ggIE_outdiagPrime_F4Two (K := K)) (hC.2.2 K hK2))⟩

theorem ggStdSubSmallInputOn_excTwoThree (h6 : GGE6TwoNormSmallInput)
    (h7 : GGE7TwoNormSmallInput) (h8 : GGE8TwoNormSmallInput) (hF4 : GGF4TwoNormSmallInput) :
    GGStdSubSmallInputOn ExcTwoThreeLabel :=
  ggStdSubSmallInputOn_of_labels_normSmall ggLNoncyclicInput_holds fun _ _ _ _ h _ =>
    largeEvenLabelAll_normSmall_excTwoThree h6 h7 h8 hF4 h

end Certs

end CFSG.StandardType.SmallExc

end
