module

public import CFSG.LocalAnalysis.StandardType.GGQ2CentInner
import CFSG.LocalAnalysis.StandardType.GGTorusGenOrthTwoCent
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusForms
import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExc

public section

namespace CFSG.StandardType.GGQ2CentPort

open CFSG CFSG.Assembly

private theorem recipeOmegaPlus_q2Cent
    {l : ℕ} {Q : LargeEvenRawCont}
    (hl : 4 ≤ l) (h : LargeEvenRecipeOmegaPlus l (2 ^ 1) Q) :
    LargeEvenRecipeOmegaPlus l (2 ^ 1) fun R _ I F => Q R I F ∧
      (GGTorusCentSC 3 R ∧ (∀ φ ∈ I, φ ^ 3 = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R)) ∧
        GGCenterPrime 3 R) := by
  obtain ⟨K, hfield, hfinite, hK, hQ⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (R := K) (p := 2) (f := 1)
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
  obtain ⟨n, rfl⟩ : ∃ n, l = n + 1 := ⟨l - 1, by omega⟩
  refine ⟨K, hfield, hfinite, hK, hQ, ?_, fun _ hφ _ => hφ,
    (OrthNs.center_data_omegaPlus Nat.prime_three (by norm_num) (by omega)).2⟩
  exact ggTorusCentSC_of_mulEquiv (OrthTorus.rPlusEquiv K (by omega))
    (ggTorusCentSC_orthDerivedTwo (by rw [hK, pow_one]) (TableBOrth.nondegenerate_qPlusForm _)
      (OrthTorus.exists_totallySingular_qPlusForm (by omega)))

private theorem recipeOmegaMinus_q2Cent
    {m : ℕ} {Q : LargeEvenRawCont}
    (hm : 3 ≤ m) (h : LargeEvenRecipeOmegaMinus m (2 ^ 1) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ 1) fun R _ I F => Q R I F ∧
      (GGTorusCentSC 3 R ∧ (∀ φ ∈ I, φ ^ 3 = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R)) ∧
        GGCenterPrime 3 R) := by
  obtain ⟨K, hfield, hfinite, hK, b, c, hbc, hQ⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (R := K) (p := 2) (f := 1)
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
  obtain ⟨-, hT⟩ := OrthTorus.charSum_qMinusForm m hbc
  refine ⟨K, hfield, hfinite, hK, b, c, hbc, hQ, ?_, fun _ hφ _ => hφ,
    (OrthExc.center_data_omegaMinus Nat.prime_three (by norm_num) hm hbc).2⟩
  exact ggTorusCentSC_of_mulEquiv (OrthTorus.rMinusEquiv K m b c)
    (ggTorusCentSC_orthDerivedTwo (by rw [hK, pow_one]) (TableBOrth.nondegenerate_qMinusForm m hbc)
      (hT hm))

theorem omegaTwoTransportInput_holds :
    omegaTwoTransportInput := by
  refine labelTInput_of_labelAll fun lab hlab hn ht => ?_
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hn ht
  subst hn
  intro Q hQ
  rcases ht with ⟨rfl, hl⟩ | ⟨rfl, hl⟩
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [if_neg (by omega)] at hQ ⊢
    exact recipeOmegaPlus_q2Cent hl hQ
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [if_neg (by omega), if_neg (by omega)] at hQ ⊢
    exact recipeOmegaMinus_q2Cent (by omega) hQ

end CFSG.StandardType.GGQ2CentPort

end
