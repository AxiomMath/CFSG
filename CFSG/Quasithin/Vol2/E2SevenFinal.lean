module

public import CFSG.Quasithin.Vol2.E2SevenSp4
public import CFSG.Quasithin.Vol2.E2SevenKG3
public import CFSG.Quasithin.Vol2.E2SevenKG2Sz
public import CFSG.Quasithin.Vol2.E2SevenKG1Sz
public import CFSG.Quasithin.Vol2.E2SevenKG1U3
public import CFSG.Quasithin.Vol2.E2SevenKG6
public import CFSG.Quasithin.Vol2.E2SevenKG4
public import CFSG.Quasithin.Vol2.E2SevenKG4Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

variable {G : Type} [Group G] [Finite G] {H T M V : Subgroup G}

theorem Hyp28.four_le_card_of_ne_two (h : Hyp28 H T M V) (hV : Nat.card V ≠ 2) :
    4 ≤ Nat.card V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (B6.isPGroup_of_isElemAbelian h.elem)
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · exfalso
    interval_cases k
    · rw [pow_zero, Subgroup.card_eq_one] at hk
      exact h.ne_bot hk
    · rw [pow_one] at hk
      exact hV hk
  · rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2

end E2

namespace ASInputs

open E2

theorem as_E_2_7C_of
    (hE22 : E22StatementC) (hKG4sq : KGL2OddSq) (hKG5 : KGL3Eps) (hKG7 : E27Sp4) :
    AS_E_2_7C := by
  have hKG1 := kgBenderInner_of_parts kgBenderInnerL2_holds kgBenderInnerSz_holds
    kgBenderInnerU3_holds
  have hKG1' := kgBenderInnerTwo_of_parts kgBenderInnerTwoL2_holds kgBenderInnerTwoSz_holds
  have hKG2L2 := kgBenderSubL2_holds
  have hKG2Sz := kgBenderSubSz_holds
  have hKG2U3 := kgBenderSubU3_holds
  have hKG3 := kgBenderMax_holds
  have hKG4 := kgL2Odd_of_parts kgL2OddPrime_holds hKG4sq
  have hKG4' := kgL2OddTwo_holds
  have hKG6 := kgL3Even_holds
  intro G _ _ H T M V h hJ hL33
  by_cases hsolv : Group.IsSolvable ↥H
  · exact h.exists_isInIHTVC_of_solvable hJ hsolv
  by_cases hV2 : Nat.card V = 2
  · exact exists_isInIHTVC_of_card_two_e22 hE22 h hJ hsolv hV2
  have hV4 := h.four_le_card_of_ne_two hV2
  obtain ⟨⟨K, hKc, hHK, hq, hcases⟩, hSQs⟩ := hE22.1 G H T M h.minParabolic h.sqtk hsolv
  have hNP := hE22.2 G H T M K h.minParabolic h.sqtk hsolv hKc hHK hq hcases hSQs
  have hKH : K ≤ H := le_of_mem_cComp hKc
  dsimp only [E22CasesNoN] at hcases
  dsimp only [E22NParamCases] at hNP
  rcases hcases with ⟨hJQ, t, ht, hne, hM, h1⟩ | ⟨hTK, hJ2, h2⟩
  · obtain ⟨hA, hB⟩ := hNP.1 hJQ ⟨t, ht, hne, hM⟩
    rcases h1 with ⟨n, hn, hty, hBor⟩ | ⟨p, hp, hp8, hK, hMK, haut⟩
    ·
      have hP := pairCase_of h hJ hKc hHK ht hne (isSimpleGroup_of_psl_or_sz hty)
      have eK := equivStarOfKerInEqBot hJ hKH
      have hty' : IsPSL 2 2 n ↥K ∨ IsSz n ↥K :=
        hty.imp (isPSL_of_mulEquiv eK) (isSz_of_mulEquiv' eK)
      have hnH := nParam_eq_of_pairCase hKG3 h hJ hP hn hty' (hA n hn hty hBor)
      exact exists_isInIHTVC_of_bender_two hKG1' hKG2L2 hKG2Sz h hJ hKc hHK ht hne hM hn hty hBor
        hnH hV4
    ·
      exact exists_isInIHTVC_of_l2two hKG4' h hJ hKc hHK ht hne hM hp hp8 hK hMK haut
        (hB p hp hp8 hK hMK haut) hV4
  · obtain ⟨h2a, h2b, -, -⟩ := hNP.2 hTK hJ2
    rcases h2 with ⟨n, hBen, hBor⟩ | ⟨n, hn, hty, hD, hBor⟩ |
        ⟨p, e, hp, hp3, he, hpe, hK, hMK, haut⟩ | ⟨p, hp, hp2, hK, hMK⟩
    ·
      exact exists_isInIHTVC_of_bender hKG1 hKG2L2 hKG2Sz hKG2U3 h hJ hKc hHK hTK hBen hBor
        (h2a n hBen hBor).2 hSQs hV4
    ·
      have hnstar := (h2b n hn hty hD hBor).2
      rcases hty with hL3 | hSp
      · exact exists_isInIHTVC_of_l3 hKG2L2 hKG6 h hJ hKc hHK hTK hn hL3 hD hBor hnstar hSQs hV4
      · exact exists_isInIHTVC_of_sp4 hKG7 h hJ hKc hHK hTK hn hSp hD hBor hnstar hSQs hV4
    ·
      exact (false_of_l2odd hKG4 h hJ hKc hHK hTK hp hp3 he hpe hK hMK haut hSQs hV4).elim
    ·
      exact (hL33 (isL33Exception_of_l3eps hKG5 h hJ hKc hHK hTK hp hp2 hK hMK hSQs hV4)).elim

end ASInputs

end CFSG.Quasithin
