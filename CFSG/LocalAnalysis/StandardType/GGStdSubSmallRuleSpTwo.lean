module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpRank
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallSpTwoDelta
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeSmall
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRest
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeSp

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def GGSpTwoNormSmallRFour : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    GGStdSubTwoTorusNormSmallR 3 (4 - 1) (LargeEvenProj (LargeEvenSpGroup K 4))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K 4)) (LargeEvenGSpSet K 4))

@[expose] def GGSpTwoNormSmallRHigh : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 → ∀ m : ℕ, 5 ≤ m →
    GGStdSubTwoTorusNormSmallR 3 (m - 1) (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m))

theorem ggStdSubTwoTorusNormSmallR_spTwo (h4 : GGSpTwoNormSmallRFour)
    (h5 : GGSpTwoNormSmallRHigh) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {m : ℕ}
    (hm : 3 ≤ m) :
    GGStdSubTwoTorusNormSmallR 3 (m - 1) (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)) := by
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (le_refl 1) (by rw [hK, pow_one])
  rcases (show m = 3 ∨ m = 4 ∨ 5 ≤ m by omega) with rfl | rfl | h
  · exact ggStdSubTwoTorusNormSmallR_spTwo_three hK
  · exact h4 K hK
  · exact h5 K hK m h

theorem recipeSymplectic_stdSubSmallR_spTwo {m N : ℕ} (hm : 3 ≤ m) (hN : N = 2)
    (h4 : GGSpTwoNormSmallRFour) (h5 : GGSpTwoNormSmallRHigh)
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeSymplectic m N false Q) :
    LargeEvenRecipeSymplectic m N false fun R _ I F => Q R I F ∧ GGOutdiagOdd 3 R I ∧
      ∃ r, GGTorusLift 3 r R ∧ GGStdSubTwoTorusNormSmallR 3 r R I ∧
        GGStdSubTwoTorusDeltaSmall 3 r R I := by
  subst hN
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (le_refl 1) (by rw [hK, pow_one])
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hN' := ggStdSubTwoTorusNormSmallR_spTwo h4 h5 hK hm
  rw [Nat.add_sub_cancel] at hN'
  exact ⟨K, inferInstance, inferInstance, hK, ⟨hQ, SpTwo.ggOutdiagOdd_spTwo hK hm _, k,
    TwoThree.ggTorusLift_sp_two hK, hN', SpTwo.ggStdSubTwoTorusDeltaSmall_spTwo hK hm k _⟩⟩

theorem largeEvenLabelAll_stdSubNormSmallR_spTwo {p : ℕ} {lab : LargeEvenLabel}
    (h4 : GGSpTwoNormSmallRFour) (h5 : GGSpTwoNormSmallRHigh)
    (hlab : LargeEvenInLambda2 lab) (h : GGSpTwoThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagOdd p R I ∧ ∃ r, GGTorusLift p r R ∧
      GGStdSubTwoTorusNormSmallR p r R I ∧ GGStdSubTwoTorusDeltaSmall p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨rfl, hn, ht⟩ := h
  dsimp only at hn ht
  subst hn
  intro Q hQ
  rcases ht with rfl | rfl
  · have hl : 3 ≤ l := by
      have h1 := hlab.2
      dsimp only at h1
      omega
    exact recipeSymplectic_stdSubSmallR_spTwo hl (by norm_num) h4 h5 hQ
  · have hl : 3 ≤ l := by
      have h1 := hlab.2
      dsimp only at h1
      omega
    exact recipeSymplectic_stdSubSmallR_spTwo hl (by norm_num) h4 h5 hQ

theorem ggStdSubSmallInputOn_spTwo_of_rule (h4 : GGSpTwoNormSmallRFour)
    (h5 : GGSpTwoNormSmallRHigh) :
    GGStdSubSmallInputOn GGSpTwoThreeLabel :=
  ggStdSubSmallInputOn_of_labels_normSmallR ggLNoncyclicInput_holds fun _ _ _ hlab hS _ =>
    largeEvenLabelAll_stdSubNormSmallR_spTwo h4 h5 hlab hS

theorem ggStdSubSmallInputOn_of_not_spTwo' (h4 : GGSpTwoNormSmallRFour)
    (h5 : GGSpTwoNormSmallRHigh)
    {T : ℕ → LargeEvenLabel → Prop}
    (h : GGStdSubSmallInputOn fun p lab => T p lab ∧ ¬ GGSpTwoThreeLabel p lab) :
    GGStdSubSmallInputOn T :=
  ((ggStdSubSmallInputOn_spTwo_of_rule h4 h5).or h).mono fun p lab hT => by
    by_cases hl : GGSpTwoThreeLabel p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hT, hl⟩

end CFSG.StandardType
