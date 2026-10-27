module

public import CFSG.Quasithin.Vol2.Ch8Sec2L825K
public import CFSG.Quasithin.Vol2.Ch8Sec2L8210
public import CFSG.Quasithin.Vol2.Ch8Sec2L825A
public import CFSG.Quasithin.Vol2.Ch8Sec2L825C
public import CFSG.Quasithin.Vol2.Ch8Sec2L825J

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs
open scoped IsMulCommutative

section L825L

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem rk_eq_of_card_82 {V : Subgroup G} {n : ℕ} (h : Nat.card ↥V = 2 ^ n) : rk ↥V = n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold rk
  rw [h, padicValNat.prime_pow]

theorem rk_pos_82 {V : Subgroup G} (hV : IsPGroup 2 ↥V) (h1 : V ≠ ⊥) : 0 < rk ↥V := by
  rcases Nat.eq_zero_or_pos (rk ↥V) with h0 | h0
  · exfalso
    apply h1
    have hc := card_eq_two_pow_of_isPGroup hV
    rw [h0, pow_zero] at hc
    exact Subgroup.eq_bot_of_card_eq V hc
  · exact h0

theorem seven_le_rParam_82 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h325 : Stmt3_2_5) (hin : Input8_1_2) (h755 : Input7_5_5)
    (htab : HTab82) (hcode : HCode82) (hcard : Mathieu.StmtH13Card)
    (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I) [IsMulCommutative ↥(fsuV T I)]
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hV : IsElemAbelian 2 (fsuV T I))
    (hrow : Row711M24Code T L I) : (7 : ℕ∞) ≤ rParam (fsuV T I) := by
  obtain ⟨-, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hL0 : fsuL0 T L = L := fsuL0_eq_of_le_normalizer hTL
  have hML : fsuM T L ≤ Subgroup.normalizer (L : Set G) := by
    show Subgroup.normalizer (fsuL0 T L : Set G) ≤ _
    rw [hL0]
  have hTI : IsTISetUnder (fsuV T I) (fsuM T L) :=
    isTISetUnder_of_stmt3_2_5_of_le_normalizer h325 hyp.fsu hTL
  have hrow' : MathieuCode24 (autI hV (fsuL0 T L)) ⊤ ⊥ := hrow
  obtain ⟨-, -, hT24⟩ := htab (IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) (autI hV ⊤)
    (isOver_autI_82 hV hNM)
  obtain ⟨hc24, -⟩ := hcode (IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) (autI hV ⊤)
    (isOver_autI_82 hV hNM)
  obtain ⟨hβ, h166⟩ := hc24 hrow'
  obtain ⟨-, -, hα⟩ := hT24 hrow'
  have hV11 : rk ↥(fsuV T I) = 11 :=
    rk_eq_of_card_82 ((hcard ↥(fsuV T I) (autOn (fsuL0 T L) (fsuV T I))).1 (Or.inr hrow))
  unfold rParam
  refine le_iInf₂ fun U hU => ?_
  obtain ⟨hUV, hC⟩ := hU
  have h6 := lt_mQuot_of_odd_82 h37 h38 h39 hmod h325 hin h755 hyp h731 hML hV hTI (m := 6)
    (by norm_num) (by omega) (lt_of_lt_of_le (by norm_num) hα) (fun y hy hy1 hyo hyU => by
      obtain ⟨hy3, hy6⟩ := (hβ y hy hy1 hyo hyU)
      exact ⟨hy6, hy3, h166 _ (Subgroup.zpowers_le.mpr hy)
        (by rw [Nat.card_zpowers, hy3]) hy6⟩) hUV hC
  exact_mod_cast h6

theorem bounds_82 (hmod : StmtFSUModule) (h734 : Stmt7_3_4) (hyp : Hyp7_0_2 G T L I)
    (h731 : Hyp7_3_1 T L I) {H : Subgroup G} {h : G} {k : ℕ} (hH : IsHStar T (fsuM T L) H)
    (hC : Concl822 T L I H h k) (hV : IsElemAbelian 2 (fsuV T I)) :
    wParam T (fsuV T I) ≤ (k : ℕ∞) ∧ (k : ℕ∞) ≤ (nPrime (autI hV ⊤) : ℕ∞) ∧
      mQuot (B6.conjSub h (fsuV T I)) (ch82A (fsuV T I) h) = k ∧
      ¬ ch82A (fsuV T I) h ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  obtain ⟨-, hN⟩ := hmod G T L I hyp.fsu
  obtain ⟨-, -, -, hZ1, -, hSyl, -, -, hkn, -, -, -, -, hAC, -, hAC', hm, -, -, -, -⟩ := hC
  have hAT : ch82A (fsuV T I) h ≤ T := fun x hx =>
    (CFSG.QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSyl hx.2).1
  have hk' := mQuot_conjSub_ch82A_82 hV hAC hm
  have hVp : IsPGroup 2 ↥(fsuV T I) := B2F.isPGroup_of_isElemAbelian hV
  have hkV : k < rk ↥(fsuV T I) := by
    have h1 := mQuot_add_rk (A := fsuV T I) (B := ch82ZI (fsuV T I) h) inf_le_left
    have hZp : IsPGroup 2 ↥(ch82ZI (fsuV T I) h) := hVp.to_le inf_le_left
    have h2 : 0 < rk ↥(ch82ZI (fsuV T I) h) := rk_pos_82 hZp hZ1
    omega
  obtain ⟨hHs, -, -, -⟩ := h734 G T L I hyp h731 hV
  have hev : ¬ Odd (Nat.card ↥H) := by
    intro hodd
    have hVH : fsuV T I ≤ H := (fsuV_le_T hyp.fsu hV hN).trans hH.1.1
    have h1 := Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hVH)
    rw [card_eq_two_pow_of_isPGroup hVp] at h1
    have h2 := rk_pos_82 hVp fun hb => hZ1 (le_bot_iff.mp (hb ▸ inf_le_left))
    exact absurd h1 (Nat.not_odd_iff_even.mpr ((Nat.even_pow' h2.ne').mpr even_two))
  exact ⟨wParam_le_82 hV hAT hk' hkV hAC', (le_nParam_82 hkn hev).trans (hHs H hH).2, hk', hAC'⟩

theorem l3_k_eq_82 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h325 : Stmt3_2_5) (hin : Input8_1_2) (h711n : Stmt7_1_1_normal)
    (h734 : Stmt7_3_4) (h756 : Stmt7_5_6_two) (hE214 : AS_E_2_14) (htab : HTab82)
    (hL9 : HL3Nine82) (hdiv : Step823L3Div) (hres : Res823L3)
    (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I) (h821 : Hyp8_2_1 T L I)
    [hc : IsMulCommutative ↥(fsuV T I)] {n : ℕ} (hrow : Row711L3Nine T L I n) {H : Subgroup G}
    {h : G} {k : ℕ} (hH : IsHStar T (fsuM T L) H) (hhH : h ∈ H) (hC : Concl822 T L I H h k) :
    wParam T (fsuV T I) = (k : ℕ∞) ∧ k = n := by
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hcase : Case8_2 T L I := Or.inl ⟨n, hrow⟩
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_case82 h711n hyp hcase
  obtain ⟨hwk, hkn', -, -⟩ := bounds_82 hmod h734 hyp h731 hH hC hV
  obtain ⟨-, -, -, hn'⟩ := h734 G T L I hyp h731 hV
  have hnP : nPrime (autI hV ⊤) = 2 * n := (hn' hc).2.2.1 n hrow
  rw [hnP] at hkn'
  have hk2n : k ≤ 2 * n := by exact_mod_cast hkn'
  have hnw : (n : ℕ∞) ≤ wParam T (fsuV T I) := h756 G T L I hyp h731 hc n hrow
  rcases Nat.lt_or_ge n k with hnk | hkn2
  · exfalso
    have hdvd := dvd_of_pow_sub_one_dvd_82 hrow.1 hnk
      (hdiv G T L I hyp h731 h821 hc hcase H h k hH hhH hC n hrow hnk)
    rcases eq_two_mul_or_of_dvd_82 hnk hk2n hdvd with hk | hk
    · subst hk
      obtain ⟨-, hhI, hIC, hZ1, -, hSyl, hMIeq, hker, -, hcases, hVZ, hBor, hA7, -, -, -, -, -,
        h28, hchar, hTI⟩ := hC
      have hVZ' : E2.star (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) (fsuV T I) ≤
          E2.star (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h)
            (T ⊓ ch82I (fsuV T I) h) := by
        rw [hVZ]
        exact inf_le_left
      have hPSL : IsPSL 2 2 (2 * n)
          (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h)) := by
        rcases hcases with ⟨h21, -⟩ | hP | hS
        · have := hrow.1
          omega
        · exact hP
        · exact absurd hS (not_isSz_of_even_82 (even_two_mul n))
      obtain ⟨-, -, hL4, hL6, -⟩ := hL9 (IntMod (fsuV T I) hV) (autI hV (fsuL0 T L))
        (autI hV ⊤) (isOver_autI_82 hV hNM) n hrow.1 hrow.2
      obtain ⟨hT9, -, -⟩ := tab_82 (stmt7_4_1_of h37 h38 h39 hmod h325 hin) htab hyp h731 hTL
        hV hNM
      exact false_of_l3_two_mul_82 hE214 hV hrow.1 hhI hIC hZ1 h28 hchar hTI hSyl hMIeq
        hker hPSL hVZ' hBor hA7 (hT9 n hrow).1 (not_isFFModule_of_hyp702 hyp hV hNM)
        (card_of_binaryNineTensor_82 hrow.1 hrow.2) hL6 hL4
    · exact hres G T L I hyp h731 h821 hc hcase H h k hH hhH hC n hrow hk
  · have hw : wParam T (fsuV T I) = (k : ℕ∞) :=
      le_antisymm hwk ((Nat.cast_le.mpr hkn2).trans hnw)
    refine ⟨hw, le_antisymm hkn2 ?_⟩
    have := hnw.trans hw.le
    exact_mod_cast this

theorem code_k_eq_82 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h325 : Stmt3_2_5) (hin : Input8_1_2) (h711n : Stmt7_1_1_normal)
    (h734 : Stmt7_3_4) (h755 : Input7_5_5) (hE214 : AS_E_2_14) (htab : HTab82)
    (hcode : HCode82) (hcard : Mathieu.StmtH13Card)
    (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I) [hc : IsMulCommutative ↥(fsuV T I)]
    (hrow : Row711M22Code T L I ∨ Row711M24Code T L I) {H : Subgroup G} {h : G} {k : ℕ}
    (hH : IsHStar T (fsuM T L) H) (hC : Concl822 T L I H h k) :
    wParam T (fsuV T I) = (k : ℕ∞) ∧ k = 1 := by
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hcase : Case8_2 T L I := by
    rcases hrow with hr | hr
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr (Or.inl hr))
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_case82 h711n hyp hcase
  have hFF := not_isFFModule_of_hyp702 hyp hV hNM
  obtain ⟨hwk, hkn', -, -⟩ := bounds_82 hmod h734 hyp h731 hH hC hV
  obtain ⟨-, -, -, hn'⟩ := h734 G T L I hyp h731 hV
  have hnP : nPrime (autI hV ⊤) = 2 := by
    rcases hrow with hr | hr
    · exact (hn' hc).2.2.2.1 (Or.inr (Or.inr (Or.inl hr)))
    · exact (hn' hc).2.2.2.1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr)))))))
  rw [hnP] at hkn'
  have hk2 : k ≤ 2 := by exact_mod_cast hkn'
  have hfw := lemma_7_5_1 hyp hV hN hNM
  obtain ⟨-, hT22, hT24⟩ := tab_82 (stmt7_4_1_of h37 h38 h39 hmod h325 hin) htab hyp h731 hTL
    hV hNM
  have hm2r : CFSG.Open.pRank 2 (autI hV ⊤) ≤ 6 ∧
      ((CFSG.Open.pRank 2 (autI hV ⊤) : ℕ) : ℕ∞) + 1 ≤ rParam (fsuV T I) := by
    rcases hrow with hr | hr
    · obtain ⟨hm2, hr6⟩ := hT22 hr
      refine ⟨hm2.trans (by norm_num), le_trans ?_ hr6⟩
      exact_mod_cast Nat.succ_le_succ hm2
    · obtain ⟨hm2, -, -, -⟩ := hT24 hr
      refine ⟨hm2, le_trans ?_
        (seven_le_rParam_82 h37 h38 h39 hmod h325 hin h755 htab hcode hcard hyp h731 hTL hV hr)⟩
      exact_mod_cast Nat.succ_le_succ hm2
  have hw1 : (1 : ℕ∞) ≤ wParam T (fsuV T I) := by
    refine Order.one_le_iff_ne_zero.mpr fun hw0 => ?_
    rw [hw0, add_zero] at hfw
    have h1 := hm2r.2.trans hfw
    have h2 : ((CFSG.Open.pRank 2 (autI hV ⊤) : ℕ) : ℕ∞) < _ + 1 :=
      ENat.lt_add_one_iff (ENat.natCast_ne_top _) |>.mpr le_rfl
    exact absurd h1 (not_le.mpr h2)
  have hk1 : 1 ≤ k := by exact_mod_cast hw1.trans hwk
  have hk : k = 1 := by
    rcases (show k = 1 ∨ k = 2 by omega) with hk | hk
    · exact hk
    · subst hk
      exfalso
      obtain ⟨-, hhI, hIC, hZ1, -, hSyl, hMIeq, hker, -, hcases, hVZ, hBor, hA7, -, -, -, -, -,
        h28, hchar, hTI⟩ := hC
      have hVZ' : E2.star (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) (fsuV T I) ≤
          E2.star (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h)
            (T ⊓ ch82I (fsuV T I) h) := by
        rw [hVZ]
        exact inf_le_left
      obtain ⟨-, h167⟩ := hcode (IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) (autI hV ⊤)
        (isOver_autI_82 hV hNM)
      have hPSL : IsPSL 2 2 2
          (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h)) := by
        rcases hcases with ⟨h21, -⟩ | hP | hS
        · omega
        · exact hP
        · exact absurd hS (not_isSz_of_even_82 even_two)
      exact false_of_code_two_82 hE214 hV (fsuV_le_T hyp.fsu hV hN) (le_sup_right.trans hN)
        hhI hIC hZ1 h28 hchar hTI hSyl hMIeq hker hPSL hVZ' hBor hA7 hm2r.1 hFF (h167 hrow)
  subst hk
  exact ⟨le_antisymm hwk (by exact_mod_cast hw1), rfl⟩

theorem cocode_k_eq_82 (hmod : StmtFSUModule) (h734 : Stmt7_3_4) (h813 : Stmt8_1_3)
    (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I) [hc : IsMulCommutative ↥(fsuV T I)]
    (hrow : Row711M24Cocode T L I) {H : Subgroup G} {h : G} {k : ℕ}
    (hH : IsHStar T (fsuM T L) H) (hC : Concl822 T L I H h k) :
    wParam T (fsuV T I) = (k : ℕ∞) ∧ k = 2 := by
  obtain ⟨hV, -⟩ := hmod G T L I hyp.fsu
  obtain ⟨hwk, hkn', -, -⟩ := bounds_82 hmod h734 hyp h731 hH hC hV
  obtain ⟨-, -, -, hn'⟩ := h734 G T L I hyp h731 hV
  have hnP : nPrime (autI hV ⊤) = 2 := (hn' hc).2.2.2.1
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hrow)))))))
  rw [hnP] at hkn'
  obtain ⟨-, -, hw2, -, -⟩ := h813 G T L I hyp h731 hc (Or.inr (Or.inr hrow))
  rw [hw2] at hwk
  have h1 : 2 ≤ k := by exact_mod_cast hwk
  have h2 : k ≤ 2 := by exact_mod_cast hkn'
  have hk : k = 2 := le_antisymm h2 h1
  subst hk
  exact ⟨hw2, rfl⟩

theorem stmt8_2_3_82 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h325 : Stmt3_2_5) (hin : Input8_1_2) (h711n : Stmt7_1_1_normal)
    (h734 : Stmt7_3_4) (h756 : Stmt7_5_6_two) (h813 : Stmt8_1_3) (h755 : Input7_5_5)
    (hE214 : AS_E_2_14) (htab : HTab82) (hL9 : HL3Nine82) (hcode : HCode82)
    (hcard : Mathieu.StmtH13Card) (hdiv : Step823L3Div) (hres : Res823L3)
    (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I) (h821 : Hyp8_2_1 T L I)
    [hc : IsMulCommutative ↥(fsuV T I)] (hrow : Case8_2 T L I) {H : Subgroup G} {h : G} {k : ℕ}
    (hH : IsHStar T (fsuM T L) H) (hhH : h ∈ H) (hC : Concl822 T L I H h k) :
    wParam T (fsuV T I) = (k : ℕ∞) ∧ IsWOffender T (fsuV T I) (ch82A (fsuV T I) h) := by
  obtain ⟨hV, -⟩ := hmod G T L I hyp.fsu
  obtain ⟨-, -, hk', hAC'⟩ := bounds_82 hmod h734 hyp h731 hH hC hV
  have hw : wParam T (fsuV T I) = (k : ℕ∞) := by
    rcases hrow with ⟨n, hrow⟩ | hrow | hrow | hrow
    · exact (l3_k_eq_82 h37 h38 h39 hmod h325 hin h711n h734 h756 hE214 htab hL9 hdiv hres hyp
        h731 h821 hrow hH hhH hC).1
    · exact (code_k_eq_82 h37 h38 h39 hmod h325 hin h711n h734 h755 hE214 htab hcode hcard hyp
        h731 (Or.inl hrow) hH hC).1
    · exact (code_k_eq_82 h37 h38 h39 hmod h325 hin h711n h734 h755 hE214 htab hcode hcard hyp
        h731 (Or.inr hrow) hH hC).1
    · exact (cocode_k_eq_82 hmod h734 h813 hyp h731 hrow hH hC).1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hA7, -⟩ := hC
  exact ⟨hw, isWOffender_ch82A_82 hA7 hk' hAC' hw⟩

end L825L

end CFSG.Quasithin.H13
