module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenSC
public import CFSG.LocalAnalysis.StandardType.GGTorusGenEvenSC
public import CFSG.LocalAnalysis.StandardType.GGTorusGenOrthTwoCent
public import CFSG.LocalAnalysis.StandardType.GGTorusGenOrthTwoComp
public import CFSG.LocalAnalysis.StandardType.GGTorusGenOmegaMinusTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExc

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggTorusGenTableB_omegaMinusTwo {K : Type} [Field K]
    [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {m : ℕ} (hm : 3 ≤ m) {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGTorusGenTableB 3 (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))
      (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))) := by
  obtain ⟨hZ, hcp⟩ :=
    OrthExc.center_data_omegaMinus (K := K) Nat.prime_three (by norm_num) hm hbc
  obtain ⟨-, hT⟩ := OrthTorus.charSum_qMinusForm m hbc
  have hQ := TableBOrth.nondegenerate_qMinusForm m hbc
  have hmeet : GGTorusCompMeetSC 3 (OrthRest.RMinus K m b c) :=
    ggTorusCompMeetSC_of_mulEquiv (OrthTorus.rMinusEquiv K m b c)
      (ggTorusCompMeetSC_orthDerivedTwo hK hQ)
  have hgen : GGTorusCompGenSC 3 (OrthRest.RMinus K m b c) := by
    rcases Nat.even_or_odd m with hev | hodd
    · exact ggTorusCompGenSC_of_evenSignedPermEltSC Nat.prime_three (by norm_num)
        (ggOrthEvenTorusInput_holds.2 K m 3 b c (by obtain ⟨k, hk⟩ := hev; omega) hev hbc
          Nat.prime_three (by rw [hK]))
        hmeet
    · exact ggTorusCompGenSC_of_signedEltSC Nat.prime_three (by norm_num)
        (ggOrthSignedTorusInput_holds.2 K m 3 b c hm hbc Nat.prime_three
          (Or.inr ⟨hodd, by rw [hK]⟩))
        hmeet
  exact ggTorusGenTableB_of_torusSC Nat.prime_three (fun φ hφ _ => hφ) hZ hcp
    (ggTorusCentSC_of_mulEquiv (OrthTorus.rMinusEquiv K m b c)
      (ggTorusCentSC_orthDerivedTwo hK hQ (hT hm)))
    hgen

theorem largeEvenLabelAll_torusGenTableB_omegaMinusTwoThree
    {p : ℕ} {lab : LargeEvenLabel}
    (h : GGOmegaMinusTwoThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB p R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hl, ht, hn, rfl⟩ := h
  dsimp only at hl ht hn
  subst ht hn
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  rw [if_neg (by omega), if_neg (by omega)] at hQ ⊢
  obtain ⟨K, hfield, hfinite, hK, b, c, hbc, hQ⟩ := hQ
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (R := K) (p := 2) (f := 1)
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
  exact ⟨K, hfield, hfinite, hK, b, c, hbc, hQ,
    ggTorusGenTableB_omegaMinusTwo (by rw [hK, pow_one]) (m := l - 1) (by omega) hbc⟩

end CFSG.StandardType
