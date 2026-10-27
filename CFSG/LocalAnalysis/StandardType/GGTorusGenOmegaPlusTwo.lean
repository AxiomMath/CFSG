module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenSC
public import CFSG.LocalAnalysis.StandardType.GGTorusGenEvenSC
public import CFSG.LocalAnalysis.StandardType.GGTorusGenOrthTwoCent
public import CFSG.LocalAnalysis.StandardType.GGTorusGenOrthTwoComp
public import CFSG.LocalAnalysis.StandardType.GGTorusGenOmegaPlusTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggTorusGenTableB_omegaPlusTwo {K : Type} [Field K]
    [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {m : ℕ} (hm : 4 ≤ m) :
    GGTorusGenTableB 3 (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))
      (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨hZ, hcp⟩ := OrthNs.center_data_omegaPlus (K := K) (m := n + 1) Nat.prime_three
    (by norm_num) (by omega)
  have hmeet : GGTorusCompMeetSC 3 (OrthRest.RPlus K (n + 1)) :=
    ggTorusCompMeetSC_of_mulEquiv (OrthTorus.rPlusEquiv K (by omega))
      (ggTorusCompMeetSC_orthDerivedTwo hK (TableBOrth.nondegenerate_qPlusForm _))
  have hgen : GGTorusCompGenSC 3 (OrthRest.RPlus K (n + 1)) := by
    rcases Nat.even_or_odd (n + 1) with hev | hodd
    · exact ggTorusCompGenSC_of_evenSignedPermEltSC Nat.prime_three (by norm_num)
        (ggOrthEvenTorusInput_holds.1 K (n + 1) 3 hm Nat.prime_three (Or.inr ⟨hev, by rw [hK]⟩))
        hmeet
    · exact ggTorusCompGenSC_of_signedEltSC Nat.prime_three (by norm_num)
        (ggOrthSignedTorusInput_holds.1 K (n + 1) 3 (by obtain ⟨k, hk⟩ := hodd; omega) hodd
          Nat.prime_three (by rw [hK]))
        hmeet
  exact ggTorusGenTableB_of_torusSC Nat.prime_three (fun φ hφ _ => hφ) hZ hcp
    (ggTorusCentSC_of_mulEquiv (OrthTorus.rPlusEquiv K (by omega))
      (ggTorusCentSC_orthDerivedTwo hK (TableBOrth.nondegenerate_qPlusForm _)
        (OrthTorus.exists_totallySingular_qPlusForm (by omega))))
    hgen

theorem largeEvenLabelAll_torusGenTableB_omegaPlusTwoThree
    {p : ℕ} {lab : LargeEvenLabel}
    (h : GGOmegaPlusTwoThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB p R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hl, ht, hn, rfl⟩ := h
  dsimp only at hl ht hn
  subst ht hn
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  rw [if_neg (by omega)] at hQ ⊢
  obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (R := K) (p := 2) (f := 1)
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
  exact ⟨K, hfield, hfinite, hK, hQ, ggTorusGenTableB_omegaPlusTwo (by rw [hK, pow_one]) hl⟩

end CFSG.StandardType
