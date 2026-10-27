module

public import CFSG.LocalAnalysis.StandardType.GGQ2CentInner
import CFSG.LocalAnalysis.StandardType.GGTorusGenSpTwoCent
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameCenter

public section

namespace CFSG.StandardType.GGQ2CentPort

open CFSG CFSG.Assembly

private theorem recipeSymplectic_q2Cent
    {l : ℕ} {Q : LargeEvenRawCont}
    (hl : 1 ≤ l) (h : LargeEvenRecipeSymplectic l (2 ^ 1) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ 1) false fun R _ I F => Q R I F ∧
      (GGTorusCentSC 3 R ∧ (∀ φ ∈ I, φ ^ 3 = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R)) ∧
        GGCenterPrime 3 R) := by
  obtain ⟨K, hfield, hfinite, hK, hQ⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (R := K) (p := 2) (f := 1)
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have : NeZero l := ⟨by omega⟩
  exact ⟨K, hfield, hfinite, hK, hQ, ggTorusCentSC_spTwo (by rw [hK, pow_one]) l,
    fun _ hφ _ => TableBSymp.sp_I_subset_inn hφ, ggCenterPrime_sp Nat.prime_three (by norm_num)⟩

theorem spTwoTransportInput_holds :
    spTwoTransportInput := by
  refine labelTInput_of_labelAll fun lab hlab hn ht => ?_
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hn ht
  subst hn
  have hl : 1 ≤ l := by
    have h1 := hlab.2
    rcases ht with rfl | rfl <;> (dsimp only at h1; omega)
  intro Q hQ
  rcases ht with rfl | rfl <;> dsimp only [LargeEvenRawDatum] at hQ ⊢ <;>
    exact recipeSymplectic_q2Cent hl hQ

end CFSG.StandardType.GGQ2CentPort

end
