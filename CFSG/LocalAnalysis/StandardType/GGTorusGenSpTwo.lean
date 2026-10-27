module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenSC
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSpTwoCent
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSpTwoComp
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeSp
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggTorusGenTableB_spTwo {K : Type} [Field K]
    [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {m : ℕ} (hm : 3 ≤ m) :
    GGTorusGenTableB 3 (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)) := by
  have : NeZero m := ⟨by omega⟩
  exact ggTorusGenTableB_of_torusSC Nat.prime_three
    (fun φ hφ _ => TableBSymp.sp_I_subset_inn hφ) TableBSymp.center_spProj_eq_bot
    (ggCenterPrime_sp Nat.prime_three (by norm_num)) (ggTorusCentSC_spTwo hK m)
    (ggTorusCompGenSC_of_signedEltSC Nat.prime_three (by norm_num)
      (ggSpNonsplitSignedEltInput_holds K m 3 (by omega) Nat.prime_three
        (by rw [hK]))
      (ggTorusCompMeetSC_spTwo hK hm))

private theorem recipeSymplectic_torusGenTableB_spTwo
    {l : ℕ} {Q : LargeEvenRawCont}
    (hl : 3 ≤ l) (h : LargeEvenRecipeSymplectic l (2 ^ 1) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ 1) false fun R _ I F =>
      Q R I F ∧ GGTorusGenTableB 3 R I := by
  obtain ⟨K, hfield, hfinite, hK, hQ⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (R := K) (p := 2) (f := 1)
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
  refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
  exact ggTorusGenTableB_spTwo (by rw [hK, pow_one]) hl

theorem largeEvenLabelAll_torusGenTableB_spTwoThree
    {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGSpTwoThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB p R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨rfl, hn, ht⟩ := h
  dsimp only at hn ht
  subst hn
  intro Q hQ
  rcases ht with rfl | rfl <;>
    dsimp only [LargeEvenRawDatum] at hQ ⊢ <;>
    exact recipeSymplectic_torusGenTableB_spTwo (by
      have h1 := hlab.2
      dsimp only at h1
      omega) hQ

end CFSG.StandardType
