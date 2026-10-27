module

public import Certificates.Kernel.Co2Cent.CaseBBound
public import Certificates.Kernel.Co2Cent.ChainLGlue
public import Certificates.Kernel.Co2Cent.CentLChk
public import CFSG.Certificates.Kernel.OrbRow.CentLSound
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo2U42

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelCo2Cent

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KC.OrbRow.CentGrp CFSG.KC.PGrp CFSG.KS CFSG.KS.Raw
  CFSG.KS.Raw.Orb CFSG.KD.Co2Cent Subgroup CFSG.Sporadic.Co2Cert
open CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest (evalW card_closure_le_of_rels)
open CFSG.HardMathSupport.Dickson.I271.U42Presentation (u42Words)

theorem lwFacts : wordEqK 2300 12 SB 17 (getS MB 0) (getS SL 0) (getLs WU 0) = true ∧
    wordEqK 2300 12 SB 17 (getS MB 0) (getS SL 1) (getLs WU 1) = true ∧
    wordEqK 2300 12 SB 17 (getS MB 0) xB (getLs WU 2) = true := by
  have h := ch17351_lw
  simp only [bAnd_iff] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem mem_of_word {y : ℕ} {g : Equiv.Perm (Fin 2300)} (hg : PRep 2300 12 y g) {t : ℕ}
    (h : wordEqK 2300 12 SB 17 (getS MB 0) y (getLs WU t) = true) : g ∈ co2P := by
  obtain ⟨hl, he⟩ := wordEqK_sound h
  obtain ⟨hr, hm⟩ := word_repB hl
  rw [← he] at hr
  rw [CFSG.KC.OrbRow.prep_unique hg hr]
  exact hm

theorem xB_facts {x : Equiv.Perm (Fin 2300)} (hx : PRep 2300 12 xB x) :
    x ∈ co2P ∧ x ^ 3 = 1 ∧ x ≠ 1 := by
  have h := ch17351_lx
  simp only [bAnd_iff] at h
  exact ⟨mem_of_word hx lwFacts.2.2, pow_eq_one_of_powIdK h.1 hx, ne_one_of_movesK h.2 hx⟩

theorem uv_mem (i : Fin 2) : uvL i ∈ co2P := by
  fin_cases i
  · exact mem_of_word (prepL (j := 0) (by norm_num)) lwFacts.1
  · exact mem_of_word (prepL (j := 1) (by norm_num)) lwFacts.2.1

theorem uv_comm {x : Equiv.Perm (Fin 2300)} (hx : PRep 2300 12 xB x) (i : Fin 2) :
    uvL i * x = x * uvL i := by
  have hj : lvOk 6 3 i.val := by
    fin_cases i
    · exact lvOk_iff.2 ⟨by norm_num, by decide⟩
    · exact lvOk_iff.2 ⟨by norm_num, by decide⟩
  have hu : ∀ z : Fin 2300, ((uvL i) z : ℕ) = pg 12 4095 (getS SL i.val) z :=
    fun z => (prepL (j := i.val) (by omega) z).symm
  have hxz : ∀ z : Fin 2300, (x z : ℕ) = pg 12 4095 xB z := fun z => (hx z).symm
  apply Equiv.ext
  intro y
  apply Fin.ext
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hu, hxz, hxz, hu]
  exact lvCommK_sound ch17351_lc hj y.2

theorem Lg_le {x : Equiv.Perm (Fin 2300)} (hx : PRep 2300 12 xB x) : Lg ≤ centP co2P x := by
  rw [Lg, closure_le]
  rintro _ ⟨i, rfl⟩
  exact mem_centP (uv_mem i) (uv_comm hx i)

theorem invPow_val {wd : List (ℕ × Bool)} (hwd : wd ∈ u42N) :
    ((invPow oUV wd).map sL).prod = 1 := by
  have hlet : ∀ l ∈ invPow oUV wd, l < 6 := by
    intro l hl
    obtain ⟨y, hy, rfl⟩ := mem_invPow oUV hl
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hwd
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hy
    have := z.1.2
    omega
  have hp := posWordK_rep (n := 2300) (w := 12) (by norm_num) (by norm_num) (G := getS SL)
    (σ := sL) (wd := invPow oUV wd) (fun l hl => prepL (hlet l hl))
  rw [relK_sound ch17351_lr wd hwd] at hp
  exact CFSG.KC.OrbRow.prep_unique hp (prep_pidn (by norm_num) (by norm_num))

theorem u_sq : uvL 0 * uvL 0 = 1 := by
  have h := invPow_val (wd := [(0, true), (0, true)]) (by decide)
  have e : invPow oUV [(0, true), (0, true)] = [0, 0] := rfl
  rw [e] at h
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  exact h

theorem v_pow : uvL 1 ^ 5 = 1 := by
  have h := invPow_val (wd := List.replicate 5 (1, true)) (by decide)
  have e : invPow oUV (List.replicate 5 (1, true)) = List.replicate 5 1 := rfl
  rw [e, List.map_replicate, List.prod_replicate] at h
  exact h

theorem rels_uv : ∀ w ∈ u42Words, evalW uvL w = 1 := by
  intro w hw
  rw [← invPow_prod uvL sL (fun i => rfl) oUV w ?_]
  · exact invPow_val (List.mem_map_of_mem hw)
  · rintro ⟨i, b⟩ - -
    fin_cases i
    · change uvL 0 ^ 1 = (uvL 0)⁻¹
      rw [pow_one]
      exact eq_inv_of_mul_eq_one_left u_sq
    · change uvL 1 ^ 4 = (uvL 1)⁻¹
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← pow_succ]
      exact v_pow

theorem card_Lg : Nat.card Lg = 25920 := by
  refine le_antisymm ?_ card_Lg_ge
  obtain ⟨hfin, hle⟩ := Certificates.certificate17350
  exact (card_closure_le_of_rels uvL u42Words rels_uv hfin).trans hle

theorem simple_Lg :
    IsSimpleGroup Lg ∧ ∃ a b : Lg, a * b ≠ b * a := by
  obtain ⟨e⟩ := CFSG.HardMathSupport.Dickson.I271.nonempty_mulEquiv_QP45_of_rels uvL rels_uv
    card_Lg
  exact ⟨CFSG.HardMathSupport.Dickson.I271.isSimpleGroup_of_equiv_QP45 e,
    CFSG.HardMathSupport.Dickson.I271.nonabelian_of_equiv_QP45 e⟩

theorem lfFacts : (∀ p ∈ FB, 2 ≤ p → ∃ j, lvOk 6 (getS ML 1) j ∧
      pg 12 4095 (getS SL j) p ≠ p) ∧
    ∀ i < 6, i ≠ 1 → depD (getS DL 0) (getS BB i) ≠ 255 := by
  have h := ch17351_lf
  simp only [bAnd_iff] at h
  refine ⟨movLvK_sound h.1, fun i hi hi1 => ?_⟩
  have h2 := allN_spec h.2 i hi
  have e : Nat.beq i 1 = false := by
    cases hb : Nat.beq i 1
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) hi1
  rw [e] at h2
  exact (inD_iff _ _).1 h2

theorem BL0 : getS BL 0 = 0 := by decide +kernel

theorem fix_of_centL
    {x : Equiv.Perm (Fin 2300)} (hx : PRep 2300 12 xB x) {g : Equiv.Perm (Fin 2300)}
    (hg : g ∈ centP co2P x) (hgL : ∀ l ∈ Lg, l * g = g * l) : g ∈ Cs x 6 := by
  have hcomm : ∀ l ∈ Lg, ∀ y, l (g y) = g (l y) := by
    intro l hl y
    have := congrArg (fun σ : Equiv.Perm (Fin 2300) => σ y) (hgL l hl)
    simpa only [Equiv.Perm.mul_apply] using this
  have hb1 := fix_b1 hx g hg
  have hx0 : x (bL 0) = bL 0 := (fixB hx _).2 (mem_FB.2 ⟨0, by norm_num, by
    rw [bL_def]
    simp only [BL0]
    decide +kernel⟩)
  have hgx : x (g (bL 0)) = g (bL 0) := by
    have := congrArg (fun σ : Equiv.Perm (Fin 2300) => σ (bL 0)) (comm_of_mem_centP hg)
    simp only [Equiv.Perm.mul_apply, hx0] at this
    exact this.symm
  have hp := (fixB hx _).1 hgx
  have hfixp : ∀ j, lvOk 6 (getS ML 1) j → pg 12 4095 (getS SL j) (g (bL 0)) = g (bL 0) := by
    intro j hj
    have hjL : sL j ∈ GLc 1 := subset_closure ⟨j, hj, rfl⟩
    have hs0 : sL j (bL 0) = bL 0 := GLc_fix 1 (by norm_num) _ hjL 0 (by norm_num)
    rw [← sL_apply (lvOk_iff.1 hj).1 _ (g (bL 0)).2, hcomm _ (GLc_le 1 hjL), hs0]
  have hlt : (g (bL 0) : ℕ) < 2 := by
    by_contra hge
    obtain ⟨j, hj, hne⟩ := lfFacts.1 _ hp (by omega)
    exact hne (hfixp j hj)
  have hg0 : g (bL 0) = bL 0 := by
    have hv0 : (bL 0 : ℕ) = 0 := BL0
    have hv1 : (bB 1 : ℕ) = 1 := BB1
    apply Fin.ext
    rw [hv0]
    rcases (by omega : (g (bL 0) : ℕ) = 0 ∨ (g (bL 0) : ℕ) = 1) with h0 | h1
    · exact h0
    · exfalso
      have e : g (bL 0) = g (bB 1) := by
        rw [hb1]
        exact Fin.ext (h1.trans hv1.symm)
      have := congrArg Fin.val (g.injective e)
      rw [hv0, hv1] at this
      exact absurd this (by norm_num)
  refine ⟨hg, hg.2, fun t ht => ?_⟩
  rcases eq_or_ne t 1 with rfl | ht1
  · exact hb1
  · obtain ⟨l, hl, hly⟩ := reach_L (i := 0) (by norm_num) (y := bB t) (by
      rw [bB_def]
      exact lfFacts.2 t ht ht1)
    rw [← hly, ← hcomm l (GLc_le 0 hl), hg0]

theorem caseB
    {x : Equiv.Perm (Fin 2300)} (hx : PRep 2300 12 xB x) :
    x ^ 3 = 1 ∧ x ≠ 1 ∧ x ∈ co2P ∧ Nat.card Lg = 25920 ∧ Lg ≤ centP co2P x ∧
      (∀ g ∈ centP co2P x, ∀ l ∈ Lg, g * l * g⁻¹ ∈ Lg) ∧
      (∀ g ∈ centP co2P x, (∀ l ∈ Lg, l * g = g * l) → g ^ 3 = 1) ∧
      ∀ w ∈ u42Words, evalW uvL w = 1 := by
  obtain ⟨hxP, hx3, hx1⟩ := xB_facts hx
  have hLC := Lg_le hx
  have hc : ∀ l ∈ Lg, l * x = x * l := fun l hl => comm_of_mem_centP (hLC hl)
  have hxC : x ∈ centP co2P x := mem_centP hxP rfl
  obtain ⟨hs, hnab⟩ := simple_Lg
  have hxL := CentLGrp.not_mem_of_simple Lg hnab hx1 hc
  have hperf := CentLGrp.commutator_eq_top_of_simple (L := Lg) hnab
  have hcard : Nat.card (centP co2P x) ≤ 6 * Nat.card Lg := by
    rw [card_Lg]
    exact (card_centB_le hx).trans (by norm_num)
  refine ⟨hx3, hx1, hxP, card_Lg, hLC,
    CentLGrp.conj_mem_of_card _ _ hxC hLC hc hx3 hxL hperf hcard, fun g hg hgL => ?_, rels_uv⟩
  have hgC := fix_of_centL hx hg hgL
  have hxC6 : x ∈ Cs x 6 := ⟨hxC, hxP, fun t ht => fix_bB hx ht⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hdvd := Subgroup.orderOf_dvd_natCard (Cs x 6) hxC6
  rw [hox] at hdvd
  have hc3 : Nat.card (Cs x 6) = 3 :=
    le_antisymm (Cs6_le hx) (Nat.le_of_dvd Nat.card_pos hdvd)
  have hg3 := Subgroup.orderOf_dvd_natCard (Cs x 6) hgC
  rw [hc3] at hg3
  exact orderOf_dvd_iff_pow_eq_one.1 hg3

end CertificateChecks.KernelCo2Cent

end
