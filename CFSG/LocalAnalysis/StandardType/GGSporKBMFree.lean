module

public import CFSG.LocalAnalysis.StandardType.GGSporKB7b
public import CFSG.LocalAnalysis.StandardType.GGSporKB7c
public import CFSG.LocalAnalysis.StandardType.GGSporKAssemblyK
public import CFSG.LocalAnalysis.StandardType.GGSporKInnerB
public import CFSG.LocalAnalysis.StandardType.GGSporKInnerM
public import CFSG.LocalAnalysis.StandardType.GGSporKOrdersB
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7
public import CFSG.LocalAnalysis.StandardType.GGSporKOrdersM
public import CFSG.LocalAnalysis.StandardType.GGSporKPPrimeCore
public import CFSG.LocalAnalysis.StandardType.GGSporKNoLieComp
public import CFSG.LocalAnalysis.StandardType.GGSporKB3K
public import CFSG.LocalAnalysis.StandardType.GGSporKB5K
public import CFSG.LocalAnalysis.StandardType.GGSporKM3K
public import CFSG.LocalAnalysis.StandardType.GGSporKM13Wide
public import CFSG.LocalAnalysis.StandardType.GGSporKElevenComp
public import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMAsmB
public import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMAsmM35
public import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMAsmM713
public import CFSG.LocalAnalysis.StandardType.GGSporKLieZB
public import CFSG.LocalAnalysis.StandardType.GGSporKBSevenCompNative
public import CFSG.LocalAnalysis.StandardType.GGSporKM5Wide
public import CFSG.LocalAnalysis.StandardType.GGSporKM7Wide

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

theorem ggKGroupFusionAtFlatKPair_of_finite {s : TauCeti.SporadicName} {p : ℕ}
    (h : Finite (TauCeti.CFSGIndex.sporadic s).Group → GGKGroupFusionAtFlatKPair s p) :
    GGKGroupFusionAtFlatKPair s p := by
  intro W _ _ hW q H E i hi hyp hL hK he
  have hfin : Finite (TauCeti.CFSGIndex.sporadic s).Group := by
    obtain ⟨rfl, rfl⟩ := hi
    obtain ⟨e⟩ := he
    exact Finite.of_equiv ↥(CFSG.generalizedFitting W) e.toEquiv
  exact h hfin W hW q H E i hi hyp hL hK he

private theorem gkF_factorization_seven {K : Type}
    (h : Nat.card K = 4154781481226426191177580544000000) :
    (Nat.card K).factorization 7 = 2 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [h, Nat.factorization_def _ (Fact.out : Nat.Prime 7),
    show (4154781481226426191177580544000000 : ℕ) = 7 ^ 2 * 84791458800539310024032256000000 by
      norm_num,
    padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem ggKGroupFusionAtFlatK_BM_free :
    GGKGroupFusionAtFlatK GGKFSporadicBM := by
  refine GGKGroupFusionAtFlatK.of_pairs (S := GGKFSporadicBM) (fun i p h => ?_)
    (fun s p hs => ?_)
  · rcases h with rfl | rfl
    · exact ⟨.B, rfl⟩
    · exact ⟨.M, rfl⟩
  · have hs' : s = .B ∨ s = .M := by
      rcases hs with h | h
      · exact Or.inl (TauCeti.CFSGIndex.sporadic.inj h)
      · exact Or.inr (TauCeti.CFSGIndex.sporadic.inj h)
    by_cases hp2 : ¬ p.Prime ∨ p = 2
    · exact ggSporK_pair_of_not_odd_prime s p hp2
    push Not at hp2
    obtain ⟨hp, hpne⟩ := hp2
    refine ggKGroupFusionAtFlatKPair_of_finite (fun hfin => ?_)
    rcases hs' with rfl | rfl
    · by_cases hsq : p ^ 2 ∣ Nat.card (TauCeti.CFSGIndex.sporadic .B).Group
      · rw [ggSporK_card_sporadicB] at hsq
        rcases ggSporK_sq_dvd_B hp hsq with rfl | rfl | rfl | rfl
        · exact absurd rfl hpne
        · exact ggSporK_pair_of_inputsAK_of_simple .B 3 (fun _ => ggSporK_inner_B)
            (fun _ => ⟨ggSporK_bmNoLiePComp_B_three, ggSporK_bmPPrimeCore_B_three,
              ggSporK_bmCentreZ_B_three, bmOrd_B_three⟩)
        · exact ggSporK_pair_of_inputsAK_of_simple .B 5 (fun _ => ggSporK_inner_B)
            (fun _ => ⟨ggSporK_bmNoLiePComp_B_five, ggSporK_bmPPrimeCore_B_five,
              ggSporK_bmCentreZ_B_five, bmOrd_B_five⟩)
        · exact ggSporK_pair_of_inputsB_of_simple .B (fun _ => ggSporK_inner_B)
            (fun _ => ggSporK_bSevenComp_B) (fun _ => ggSporK_bSevenCentAbelian_B)
            (fun _ => ggSporK_bSevenSpread_B ggSporK_bSevenComp_B) (fun _ => bSevenOrd_B)
            (fun _ => lieSevenOddCentre7sq_B) (gkF_factorization_seven ggSporK_card_sporadicB)
      · exact ggSporK_pair_of_not_sq_dvd_card_of_simple .B p (fun _ => ggSporK_inner_B) hsq
    · by_cases hsq : p ^ 2 ∣ Nat.card (TauCeti.CFSGIndex.sporadic .M).Group
      · rw [ggSporK_card_sporadicM] at hsq
        rcases ggSporK_sq_dvd_M hp hsq with rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd rfl hpne
        · exact ggSporK_pair_of_inputsAK_of_simple .M 3 ggSporK_inner_M_of_simple
            (fun hS => ⟨ggSporK_bmNoLiePComp_M_three, ggSporK_bmPPrimeCore_M_three_of_simple hS,
              ggSporK_bmCentreZ_M_three_of_simple hS, bmOrd_M_three⟩)
        · exact ggSporK_pair_of_inputsAK_of_simple .M 5 ggSporK_inner_M_of_simple
            (fun hS => ⟨ggSporK_bmNoLiePComp_M_five, ggSporK_bmPPrimeCore_M_five_of_simple hS,
              ggSporK_bmCentreZ_M_five_of_simple hS, bmOrd_M_five⟩)
        · exact ggSporK_pair_of_inputsAK_of_simple .M 7 ggSporK_inner_M_of_simple
            (fun hS => ⟨fun _ => ggSporK_bmNoLiePComp_M_seven,
              ggSporK_bmPPrimeCore_M_seven_of_simple hS, ggSporK_bmCentreZ_M_seven_of_simple hS,
              bmOrd_M_seven⟩)
        · exact ggSporK_pair_of_elevenComp_of_simple .M ggSporK_inner_M_of_simple
            ggSporK_bmElevenComp_M_of_simple
        · exact ggSporK_pair_of_inputsAK_of_simple .M 13 ggSporK_inner_M_of_simple
            (fun hS => ⟨fun _ => ggSporK_bmNoLiePComp_M_thirteen,
              ggSporK_bmPPrimeCore_M_thirteen_of_simple hS,
              ggSporK_bmCentreZ_M_thirteen_of_simple hS, bmOrd_M_thirteen⟩)
      · exact ggSporK_pair_of_not_sq_dvd_card_of_simple .M p ggSporK_inner_M_of_simple hsq

end CFSG.StandardType.SporadicShape
