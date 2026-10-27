module

public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptA312GenOdd
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptA312GenSpor
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptA312GenSL3

public section

namespace CFSG.Quasithin.H13.NF314ptA312

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.InspA312
open scoped Pointwise

theorem p_eq_seven_of_dvd_168 {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (h : p ∣ 168) : p = 7 := by
  have hle : p ≤ 168 := Nat.le_of_dvd (by norm_num) h
  interval_cases p <;> first | rfl | (exfalso; revert h; norm_num; done) | (exfalso; revert hp; norm_num; done)

theorem p_eq_seven_of_dvd {p m : ℕ} (hp : p.Prime) (hp3 : 3 < p) (h : p ∣ 168 * 2 ^ m) :
    p = 7 := by
  rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
  · exact p_eq_seven_of_dvd_168 hp hp3 h1
  · exfalso
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h1
    have := Nat.le_of_dvd (by norm_num) h2
    omega

theorem p_eq_seven_of_mul {p m : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (h : p * (p ^ 2 - 1) = 168 * 2 ^ m) : p = 7 :=
  p_eq_seven_of_dvd hp hp3 (h ▸ Dvd.intro _ rfl)

theorem not5_168 (m : ℕ) : ¬ 5 ∣ 168 * 2 ^ m := by
  intro h
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp h with h1 | h1
  · norm_num at h1
  · have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h1
    norm_num at this

theorem not49_168 (m : ℕ) : ¬ 49 ∣ 168 * 2 ^ m := by
  intro h
  have h7 : 7 ∣ 24 * 2 ^ m := by
    have : 168 * 2 ^ m = 7 * (24 * 2 ^ m) := by ring
    rw [this] at h
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 7)).mp (by simpa [pow_two] using h)
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp h7 with h1 | h1
  · norm_num at h1
  · have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 7) h1
    norm_num at this

theorem card_elemAb {p n : ℕ} {V : Type} [Group V] [Fact p.Prime]
    (h : CFSG.Quasithin.IsElemAbelianOfRank p n V) : Nat.card V = p ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, card_multiplicative_fin_zmod p n]

theorem card_psl3_seven {J : Type} [Group J] (h : IsPSL 3 7 1 J) : Nat.card J = 1876896 := by
  rw [(CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound J 3 7 1 h).1]
  decide

theorem card_psu3_seven {J : Type} [Group J] (h : IsPSU 3 7 1 J) : Nat.card J = 5663616 := by
  have hb := (CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound J 3 7 1 h).1
  have hg : Nat.gcd 3 (7 ^ 1 + 1) = 1 := by norm_num
  rw [hg] at hb
  norm_num [show Finset.Icc 2 3 = {2, 3} from rfl, Finset.prod_pair] at hb
  omega

theorem card_sl3_seven {J : Type} [Group J] (h : IsSL3 7 J) : Nat.card J = 5630688 := by
  obtain ⟨K, hF, hKf, hK, ⟨e⟩⟩ := h
  letI := hF
  letI := hKf
  rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_three K, hK]
  norm_num

theorem card_su3_seven {J : Type} [Group J] (h : IsSU3 7 J) : Nat.card J = 5663616 := by
  obtain ⟨K, hF, hKf, hK, ⟨e⟩⟩ := h
  letI := hF
  letI := hKf
  have hp7 : (7 : ℕ).Prime := by norm_num
  haveI : CharP K 7 := charP_of_card_sq K hp7 hK
  haveI : Fact (7 : ℕ).Prime := ⟨hp7⟩
  have hK' : Nat.card K = (7 ^ 1) ^ 2 := by rw [pow_one]; exact hK
  have hc := CFSG.SectionRank.OddCover.card_statedSU_three (K := K) (p := 7) (f := 1) hK'
  simp only [pow_one] at hc
  rw [Nat.card_congr e.toEquiv, hc]
  norm_num

theorem dvd_of_isExt {X : Type} [Group X] {PV PY : ∀ (V : Type) [Group V], Prop} {m : ℕ}
    (h : CFSG.Quasithin.IsExt X PV PY) (hY : ∀ (Y : Type) [Group Y], PY Y → m ∣ Nat.card Y) :
    m ∣ Nat.card X := by
  obtain ⟨V, hVn, -, hPY, hcard⟩ := isExt_card_eq h
  rw [hcard]
  exact Dvd.dvd.mul_left (hY _ hPY) _

theorem gen_left_card {Q : Type} [Group Q] [Finite Q] {B J : Subgroup Q}
    (hB : IsPSL 3 2 1 (↥B ⧸ CFSG.pCore 2 ↥B)) (hBJ : B ≤ J)
    (h : B = J ∨ A312Case B J ∨ A312Nonquasi B J) :
    B = J ∨ 64 ∣ Nat.card J ∨ Nat.card J = 2520 ∨ Nat.card J = 7560 ∨ Nat.card J = 58800 ∨
      Nat.card J = 1876896 ∨ Nat.card J = 5630688 ∨ Nat.card J = 5663616 ∨
      Nat.card (↥J ⧸ CFSG.oddCore ↥J) = 336 := by
  have hSB : IsSimpleGroup (↥B ⧸ CFSG.pCore 2 ↥B) := isSimpleGroup_of_isPSL hB
  have hcQ : Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = 168 := card_psl32 hB
  have heven : Even (Nat.card (↥B ⧸ CFSG.pCore 2 ↥B)) := by
    rw [hcQ]
    decide
  obtain ⟨k, hk⟩ := pCore_card_two_pow B
  have hcB : Nat.card ↥B = 168 * 2 ^ k := by
    rw [card_eq_quot_mul B, hcQ, hk]
  have hnot5 : ¬ 5 ∣ Nat.card ↥B := by
    rw [hcB]
    exact not5_168 k
  rcases h with rfl | h | h
  · exact Or.inl rfl
  · right
    unfold A312Case at h
    rcases h with h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 |
      h17 | h18 | h19 | h20
    ·
      obtain ⟨⟨n, hn⟩, -, -⟩ := h2
      have hc : Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
        card_of_isPSL_two_two hn
      exact (two_pow_card_ne_168 (two_le_of_isPSL_two_two hn) (hc.symm.trans hcQ)).elim
    ·
      obtain ⟨f, hSz, -⟩ := h3
      have h3' := CFSG.Quasithin.F134.not_three_dvd_card_of_suzukiModel
        (show CFSG.Blueprint.SuzukiModel (↥B ⧸ CFSG.pCore 2 ↥B) 2 f from hSz)
      rw [hcQ] at h3'
      exact (h3' (by norm_num)).elim
    ·
      obtain ⟨-, h4 | h4, -⟩ := h4
      · have := card_psl42 h4
        omega
      · have := card_psl52 h4
        omega
    ·
      obtain ⟨h5a, -, -⟩ := h5
      have hc := card_psl42 h5a
      rw [hcQ] at hc
      norm_num at hc
    ·
      obtain ⟨hB6, h6⟩ := h6
      rcases hB6 with hA5 | hL3
      · have := card_alt5 hA5
        exact (hnot5 (by rw [this]; norm_num)).elim
      · rcases h6 with h6 | h6
        · have := card_alt7 h6
          omega
        · have := card_hat h6
          rw [card_alternatingGroup_seven] at this
          omega
    ·
      rcases h7 with ⟨h7a, -⟩ | ⟨h7a, -⟩
      · have := card_alt6 h7a
        exact (hnot5 (by rw [this]; norm_num)).elim
      · have := card_hat h7a
        rw [card_alternatingGroup_six] at this
        exact (hnot5 (by rw [this]; norm_num)).elim
    ·
      rcases h8 with ⟨p, hp, hp3, hpB, hpJ⟩ | ⟨h8a, -⟩
      · have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
        have hBc : Nat.card ↥B = p * (p ^ 2 - 1) / 2 := card_psl2_odd hpB hodd
        have hm := mul_sq_sub_one_eq_two_mul hodd (hBc.symm.trans hcB)
        have hp7 := p_eq_seven_of_mul (m := k + 1) hp hp3 (by rw [hm]; ring)
        subst hp7
        have := card_psl2_seven_sq hpJ
        omega
      · have := card_alt5 h8a
        exact (hnot5 (by rw [this]; norm_num)).elim
    ·
      rcases h9 with ⟨s, p, hp, hp3, hpB, hJ⟩ | ⟨h9a, -⟩ | ⟨h9a, -⟩
      · have hc' : p * (p ^ 2 - 1) = 168 * 2 ^ k := (card_sl2 hp hpB).symm.trans hcB
        have hp7 := p_eq_seven_of_mul (m := k) hp hp3 hc'
        subst hp7
        rcases hJ with hJ | hJ
        · cases s
          · have := card_psu3_seven hJ
            omega
          · have := card_psl3_seven hJ
            omega
        · cases s
          · have := card_su3_seven hJ
            omega
          · have := card_sl3_seven hJ
            omega
      · have := card_alt6 h9a
        exact (hnot5 (by rw [this]; norm_num)).elim
      · have := card_hat h9a
        rw [card_alternatingGroup_six] at this
        exact (hnot5 (by rw [this]; norm_num)).elim
    ·
      obtain ⟨p, hp, hp3, hext, -⟩ := h10
      haveI := Fact.mk hp
      obtain ⟨V, hVn, hPV, -, hcard⟩ := isExt_card_eq hext
      have hVc := card_elemAb hPV
      rw [hVc] at hcard
      have hpd : p ^ 2 ∣ 168 * 2 ^ k := by
        rw [← hcB]
        exact ⟨_, hcard⟩
      have hp7 : p ∣ 168 * 2 ^ k := dvd_trans (dvd_pow_self p two_ne_zero) hpd
      have := p_eq_seven_of_dvd hp hp3 hp7
      subst this
      exact (not49_168 k (by simpa using hpd)).elim
    ·
      obtain ⟨h11a, -⟩ := h11
      have := card_alt6 h11a
      exact (hnot5 (by rw [this]; norm_num)).elim
    ·
      rcases h12 with ⟨h12a, -⟩ | ⟨h12a, -⟩
      · rcases h12a with h | h
        · exact (hnot5 (dvd_of_isExt (m := 5) h (fun Y _ hY => by
            have := card_alt5 hY
            rw [this]
            norm_num))).elim
        · exact (hnot5 (dvd_of_isExt (m := 5) h (fun Y _ hY => by
            have := card_alt6 hY
            rw [this]
            norm_num))).elim
      · rcases h12a with h | h
        · exact (hnot5 (dvd_of_isExt (m := 5) h (fun Y _ hY => by
            have := card_alt5 hY
            rw [this]
            norm_num))).elim
        · exact (hnot5 (dvd_of_isExt (m := 5) h (fun Y _ hY => by
            have := card_hat hY
            rw [card_alternatingGroup_six] at this
            rw [this]
            norm_num))).elim
    ·
      obtain ⟨h13a, h13b⟩ := h13
      have hJ := card_isSporadic_M23 h13b
      rcases h13a with h | h | h | h | h | h | h
      · have := card_M22 h
        exact (hnot5 (by rw [this]; norm_num)).elim
      · have := card_psl34 h
        exact (hnot5 (by rw [this]; norm_num)).elim
      · exact (hnot5 (dvd_of_isExt (m := 5) h (fun Y _ hY => by
          have := card_alt7 hY
          rw [this]
          norm_num))).elim
      · omega
      · omega
      · exact (hnot5 (dvd_of_isExt (m := 5) h (fun Y _ hY => by
          have := card_alt6 hY
          rw [this]
          norm_num))).elim
      · exact (hnot5 (dvd_of_isExt (m := 5) h (fun Y _ hY => by
          have := card_alt5 hY
          rw [this]
          norm_num))).elim
    ·
      obtain ⟨h14a, h14b⟩ := h14
      have hJ := card_isSporadic_M24 h14b
      rcases h14a with h | h | h | h
      · exact (hnot5 (dvd_of_isExt (m := 5) h (fun Y _ hY => by
          have := card_psl42 hY
          rw [this]
          norm_num))).elim
      · omega
      · omega
      · exact (hnot5 (dvd_of_isExt (m := 5) h (fun Y _ hY => by
          have := card_hat hY
          rw [card_alternatingGroup_six] at this
          rw [this]
          norm_num))).elim
    ·
      obtain ⟨h15a, -⟩ := h15
      have := card_alt5 h15a
      exact (hnot5 (by rw [this]; norm_num)).elim
    ·
      obtain ⟨h16a, -⟩ := h16
      exact (hnot5 (dvd_of_isExt (m := 5) h16a (fun Y _ hY => by
        have := card_alt5 hY
        rw [this]
        norm_num))).elim
    ·
      obtain ⟨h17a, -⟩ := h17
      have := card_J4 h17a
      omega
    ·
      obtain ⟨h18a, h18b⟩ := h18
      have hJ := card_isSporadic_HS h18b
      rcases h18a with h | h
      · exact (hnot5 (dvd_of_isExt (m := 5) h (fun Y _ hY => by
          have := card_alt5 hY
          rw [this]
          norm_num))).elim
      · omega
    ·
      obtain ⟨h19a, h19b⟩ := h19
      have hJ := card_isSporadic_He h19b
      rcases h19a with h | h
      · omega
      · exact (hnot5 (dvd_of_isExt (m := 5) h (fun Y _ hY => by
          have := card_hat hY
          rw [card_alternatingGroup_six] at this
          rw [this]
          norm_num))).elim
    ·
      obtain ⟨-, -, h20c⟩ := h20
      have := card_isSporadic_Ru h20c
      omega
  ·
    right
    dsimp only [A312Nonquasi] at h
    set OL : Subgroup Q := (CFSG.oddCore ↥J).map J.subtype with hOL
    have hBN : B ≤ Subgroup.normalizer (OL : Set Q) := le_normalizer_oddCore hBJ
    rcases h with ⟨-, hJ, p, hp, hp2, hSL⟩ | ⟨-, -, N, hNn, hNeq, hSL5⟩
    ·
      have hc := card_quot_oddCore_eq_of_sup hBJ hSB heven hJ.le
      have hq := card_sl2 hp hSL
      have hpeq : p * (p ^ 2 - 1) = 168 * 2 ^ k := hq.symm.trans (hc.trans hcB)
      have hp3 : p = 3 ∨ 3 < p := by
        have := hp.two_le
        omega
      rcases hp3 with rfl | hp3
      · norm_num at hpeq
        omega
      · have h7 := p_eq_seven_of_mul hp hp3 hpeq
        subst h7
        norm_num at hq
        omega
    ·
      subst hNeq
      have hγ := surj_of_cover (le_sup_left : B ≤ B ⊔ OL) (OL.subgroupOf (B ⊔ OL))
        (cover_of_sup le_sup_left OL hBN le_rfl (OL.subgroupOf (B ⊔ OL)) (fun o ho hol =>
          ⟨⟨o, hol⟩, (Subgroup.mem_subgroupOf).mpr ho, rfl⟩))
      have hd := card_dvd_of_surj _ hγ
      have h120 := card_sl2 (by norm_num : Nat.Prime 5) hSL5
      rw [h120] at hd
      exact (hnot5 (dvd_trans (by norm_num) hd)).elim

end CFSG.Quasithin.H13.NF314ptA312
