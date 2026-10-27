module

public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptA312GenLeft
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptA312GenSL2

public section

namespace CFSG.Quasithin.H13.NF314ptA312

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.InspA312
open scoped Pointwise

theorem quot_dichotomy {Q : Type} [Group Q] [Finite Q] {B : Subgroup Q}
    (hS : IsSimpleGroup (↥B ⧸ CFSG.pCore 2 ↥B)) (V : Subgroup ↥B) [V.Normal] :
    Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) ∣ Nat.card (↥B ⧸ V) ∨
      Nat.card (↥B ⧸ V) ∣ Nat.card (CFSG.pCore 2 ↥B) := by
  let π : ↥B →* ↥B ⧸ CFSG.pCore 2 ↥B := QuotientGroup.mk' _
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hVn : (V.map π).Normal := Subgroup.Normal.map inferInstance π hπ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (V.map π) with h | h
  · left
    have hle : V ≤ CFSG.pCore 2 ↥B := by
      intro v hv
      have hmem : π v ∈ V.map π := Subgroup.mem_map_of_mem π hv
      rw [h, Subgroup.mem_bot] at hmem
      exact (QuotientGroup.eq_one_iff v).mp hmem
    have hd := Subgroup.index_dvd_of_le hle
    exact hd
  · right
    let f : ↥(CFSG.pCore 2 ↥B) →* ↥B ⧸ V := (QuotientGroup.mk' V).comp (CFSG.pCore 2 ↥B).subtype
    have hf : Function.Surjective f := by
      intro y
      induction y using QuotientGroup.induction_on with
      | H x =>
        have hx : π x ∈ V.map π := by
          rw [h]
          exact Subgroup.mem_top _
        obtain ⟨v, hv, hvx⟩ := Subgroup.mem_map.mp hx
        have hvx' : v⁻¹ * x ∈ CFSG.pCore 2 ↥B :=
          (QuotientGroup.eq (s := CFSG.pCore 2 ↥B)).mp hvx
        refine ⟨⟨v⁻¹ * x, hvx'⟩, ?_⟩
        show (QuotientGroup.mk (v⁻¹ * x) : ↥B ⧸ V) = QuotientGroup.mk x
        rw [QuotientGroup.eq]
        have hc : x⁻¹ * v * x⁻¹⁻¹ ∈ V := (inferInstance : V.Normal).conj_mem v hv x⁻¹
        rw [inv_inv] at hc
        have e : (v⁻¹ * x)⁻¹ * x = x⁻¹ * v * x := by group
        rw [e]
        exact hc
    exact card_dvd_of_surj f hf

theorem pow2_eq_of_small {N j c : ℕ} (hN : 660 ≤ N) (h : N * 2 ^ j = c) (hc : c < 1320) :
    j = 0 ∧ N = c := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simpa using h
  · exfalso
    have h2 : 2 ≤ 2 ^ j := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    have := Nat.mul_le_mul hN h2
    omega

theorem eq_of_dvd_small {N c : ℕ} (hN : 660 ≤ N) (hc0 : 0 < c) (h : N ∣ c) (hc : c < 1320) :
    N = c := by
  obtain ⟨t, rfl⟩ := h
  rcases t with _ | _ | t
  · simp at hc0
  · simp
  · exfalso
    have h2 : 2 * N ≤ N * (t + 1 + 1) := by nlinarith
    omega

theorem excl_dich {N c j : ℕ} (hN8 : N % 8 = 4) (hN660 : 660 ≤ N) (hc0 : 0 < c)
    (hc : c < 1320) (hc3 : 3 ∣ c) (hc8 : c % 8 ≠ 4 ∨ c < 660)
    (hd : N ∣ c ∨ c ∣ 2 ^ j) : False := by
  rcases hd with h | h
  · have hEq := eq_of_dvd_small hN660 hc0 h hc
    subst hEq
    omega
  · have h3 : 3 ∣ 2 ^ j := dvd_trans hc3 h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

theorem equiv_quot_oddCore_of_sup {Q : Type} [Group Q] [Finite Q] {B J : Subgroup Q}
    (hBJ : B ≤ J) (hS : IsSimpleGroup (↥B ⧸ CFSG.pCore 2 ↥B))
    (heven : Even (Nat.card (↥B ⧸ CFSG.pCore 2 ↥B)))
    (hJ : J ≤ B ⊔ (CFSG.oddCore ↥J).map J.subtype) :
    Nonempty (↥B ≃* ↥J ⧸ CFSG.oddCore ↥J) := by
  let OL : Subgroup Q := (CFSG.oddCore ↥J).map J.subtype
  have hBN : B ≤ Subgroup.normalizer (OL : Set Q) := le_normalizer_oddCore hBJ
  let f : ↥B →* ↥J ⧸ CFSG.oddCore ↥J :=
    (QuotientGroup.mk' (CFSG.oddCore ↥J)).comp (Subgroup.inclusion hBJ)
  have hcov : ∀ x : ↥J, ∃ b : ↥B, ∃ o ∈ CFSG.oddCore ↥J, x = Subgroup.inclusion hBJ b * o :=
    cover_of_sup hBJ OL hBN hJ (CFSG.oddCore ↥J) (fun o ho hoJ => by
      rw [Subgroup.mem_map] at ho
      obtain ⟨x, hx, rfl⟩ := ho
      exact ⟨x, hx, rfl⟩)
  have hsurj : Function.Surjective f := surj_of_cover hBJ (CFSG.oddCore ↥J) hcov
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro b hb
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hb
    exact inter_oddCore_eq_one hBJ hS heven b hb
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩⟩

theorem not_dvd_smooth {q n a b c d : ℕ} (hq : q.Prime) (hq11 : 11 ≤ q)
    (hn : n = 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) (h : q ∣ n) : False := by
  subst hn
  have h1 := Nat.Coprime.eq_one_of_dvd (coprime_of_small hq hq11 a b c d) h
  have := hq.two_le
  omega

theorem dvd_eleven_of_smooth {q : ℕ} (hq : q.Prime) (hq11 : 11 ≤ q) {a b c d : ℕ}
    (h : q ∣ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11) : q = 11 := by
  rcases (Nat.Prime.dvd_mul hq).mp h with h1 | h1
  · exact (not_dvd_smooth (n := 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) (a := a) (b := b) (c := c)
      (d := d) hq hq11 rfl h1).elim
  · exact (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h1

theorem dvd_eleven_or_23 {q : ℕ} (hq : q.Prime) (hq11 : 11 ≤ q) {a b c d : ℕ}
    (h : q ∣ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d * 11 * 23) : q = 11 ∨ q = 23 := by
  rcases (Nat.Prime.dvd_mul hq).mp h with h1 | h1
  · exact Or.inl (dvd_eleven_of_smooth hq hq11 h1)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h1)

theorem not_three_dvd_two_pow (j : ℕ) : ¬ 3 ∣ 2 ^ j := by
  intro h
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  norm_num at this

theorem N_dvd_of_quot {Q : Type} [Group Q] [Finite Q] {B : Subgroup Q} {N j c : ℕ}
    {V : Subgroup ↥B} [V.Normal]
    (hS : IsSimpleGroup (↥B ⧸ CFSG.pCore 2 ↥B)) (hcQ : Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = N)
    (hj : Nat.card (CFSG.pCore 2 ↥B) = 2 ^ j)
    (hc : Nat.card (↥B ⧸ V) = c) (hc3 : 3 ∣ c) : N ∣ c := by
  rcases quot_dichotomy hS V with hd | hd
  · rw [hcQ, hc] at hd
    exact hd
  · rw [hc, hj] at hd
    have h3 : 3 ∣ 2 ^ j := dvd_trans hc3 hd
    exact (not_three_dvd_two_pow j h3).elim

theorem B2_dich_false {Q : Type} [Group Q] [Finite Q] {B : Subgroup Q} {N j c : ℕ}
    {V : Subgroup ↥B} [V.Normal]
    (hS : IsSimpleGroup (↥B ⧸ CFSG.pCore 2 ↥B)) (hN8 : N % 8 = 4) (hN660 : 660 ≤ N)
    (hj : Nat.card (CFSG.pCore 2 ↥B) = 2 ^ j)
    (hcQ : Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = N)
    (hc : Nat.card (↥B ⧸ V) = c) (hc0 : 0 < c) (hc1 : c < 1320) (hc3 : 3 ∣ c)
    (hc8 : c % 8 ≠ 4 ∨ c < 660) : False := by
  rcases quot_dichotomy hS V with hd | hd
  · rw [hcQ, hc] at hd
    exact excl_dich (j := j) hN8 hN660 hc0 hc1 hc3 hc8 (Or.inl hd)
  · rw [hc, hj] at hd
    exact excl_dich hN8 hN660 hc0 hc1 hc3 hc8 (Or.inr hd)

theorem not64_of_two_N {o N x : ℕ} (ho : Odd o) (hN : N % 8 = 4) (hx : x = N * 2 * o) :
    ¬ 64 ∣ x := by
  obtain ⟨m, rfl⟩ : ∃ m, N = 4 * m := ⟨N / 4, by omega⟩
  have hm : Odd m := Nat.odd_iff.mpr (by omega)
  have hodd : (m * o) % 2 = 1 := Nat.odd_iff.mp (Odd.mul hm ho)
  have e : x = 8 * (m * o) := by rw [hx]; ring
  intro h
  rw [e] at h
  omega

theorem gen_right_card {Q : Type} [Group Q] [Finite Q] {B J : Subgroup Q} {q : ℕ}
    (hq : q.Prime) (hq24 : q % 24 = 11 ∨ q % 24 = 13)
    (hB : IsPSL 2 q 1 (↥B ⧸ CFSG.pCore 2 ↥B)) (hBJ : B ≤ J)
    (h : B = J ∨ A312Case B J ∨ A312Nonquasi B J) :
    B = J ∨ ¬ 64 ∣ Nat.card J := by
  have hq11 : 11 ≤ q := by omega
  have hq2 : q % 2 = 1 := by omega
  have hq2' : q ≠ 2 := by omega
  have hq8 : q % 8 = 3 ∨ q % 8 = 5 := by omega
  have hS : IsSimpleGroup (↥B ⧸ CFSG.pCore 2 ↥B) := isSimpleGroup_of_isPSL hB
  have hcQ : Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = q * (q ^ 2 - 1) / 2 := card_psl2_odd hB hq2
  have hN8 : q * (q ^ 2 - 1) / 2 % 8 = 4 := mod_eight_L2 hq8
  have hN660 : 660 ≤ q * (q ^ 2 - 1) / 2 := le_card_L2_eleven hq11
  have hN3 : 3 ∣ q * (q ^ 2 - 1) / 2 := three_dvd_card_L2 hq2
  have hqN : q ∣ q * (q ^ 2 - 1) / 2 := by
    have h2 : 2 ∣ q * (q ^ 2 - 1) := by
      have hsq : q ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hq2]
      exact Dvd.dvd.mul_left (by omega) q
    have hmul : q * (q ^ 2 - 1) / 2 * 2 = q * (q ^ 2 - 1) := Nat.div_mul_cancel h2
    have hq2N : q ∣ q * (q ^ 2 - 1) / 2 * 2 := by
      rw [hmul]
      exact dvd_mul_right q _
    exact Nat.Coprime.dvd_of_dvd_mul_right ((Nat.coprime_primes hq Nat.prime_two).mpr hq2') hq2N
  have hEven : Even (Nat.card (↥B ⧸ CFSG.pCore 2 ↥B)) := by
    rw [hcQ]
    exact even_iff_two_dvd.mpr (by omega)
  obtain ⟨j, hj⟩ := pCore_card_two_pow B
  have hcB : Nat.card ↥B = q * (q ^ 2 - 1) / 2 * 2 ^ j := by
    rw [card_eq_quot_mul B, hcQ, hj]
  have hBge : 660 ≤ Nat.card ↥B := by
    rw [hcB]
    have h2j : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by norm_num)
    have hm := Nat.mul_le_mul hN660 h2j
    omega
  have hqB : q ∣ Nat.card ↥B := by
    rw [hcB]
    exact dvd_mul_of_dvd_left hqN _
  have hnot3 : ¬ 3 ∣ 2 ^ j := not_three_dvd_two_pow j
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
      exact (two_pow_card_ne_of_mod_eight (two_le_of_isPSL_two_two hn) hN8 hN660
        (hc.symm.trans hcQ)).elim
    ·
      obtain ⟨f, hSz, -⟩ := h3
      have h3' := CFSG.Quasithin.F134.not_three_dvd_card_of_suzukiModel
        (show CFSG.Blueprint.SuzukiModel (↥B ⧸ CFSG.pCore 2 ↥B) 2 f from hSz)
      rw [hcQ] at h3'
      exact (h3' hN3).elim
    ·
      obtain ⟨h4a, -, -⟩ := h4
      have hc := card_psl32 h4a
      rw [hcQ] at hc
      omega
    ·
      obtain ⟨h5a, -, -⟩ := h5
      have hc := card_psl42 h5a
      rw [hcQ] at hc
      omega
    ·
      obtain ⟨h6a, -⟩ := h6
      rcases h6a with h | h
      · have := card_alt5 h
        omega
      · have := card_psl32 h
        omega
    ·
      rcases h7 with ⟨h7a, -⟩ | ⟨h7a, -⟩
      · have := card_alt6 h7a
        omega
      · have hc := card_hat h7a
        rw [card_alternatingGroup_six] at hc
        have h1080 : q * (q ^ 2 - 1) / 2 * 2 ^ j = 1080 := by rw [← hcB, hc]
        obtain ⟨-, hNeq⟩ := pow2_eq_of_small hN660 h1080 (by norm_num)
        omega
    ·
      rcases h8 with ⟨p, hp, hp3, hpB, hpJ⟩ | ⟨h8a, -⟩
      · haveI : IsSimpleGroup ↥B := isSimpleGroup_of_isPSL hpB
        have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
        have hpc : Nat.card (CFSG.pCore 2 ↥B) = 1 := by
          rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 ↥B) with h | h
          · rw [h, Subgroup.card_bot]
          · exfalso
            have hq1 : Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = 1 := by
              show Subgroup.index (CFSG.pCore 2 ↥B) = 1
              rw [h, Subgroup.index_top]
            omega
        have hcB' : Nat.card ↥B = q * (q ^ 2 - 1) / 2 := by
          rw [card_eq_quot_mul B, hcQ, hpc, mul_one]
        have hBc : Nat.card ↥B = p * (p ^ 2 - 1) / 2 := card_psl2_odd hpB hpodd
        have hm := mul_sq_sub_one_eq_two_mul hpodd (hBc.symm.trans hcB')
        have hm2 := mul_sq_sub_one_eq_two_mul hq2 (rfl : q * (q ^ 2 - 1) / 2 = q * (q ^ 2 - 1) / 2)
        have hpq : p = q := eq_of_mul_sq_sub_one_eq (by have := hp.two_le; omega)
          (by have := hq.two_le; omega) (by omega)
        have hJc : Nat.card ↥J = q ^ 2 * ((q ^ 2) ^ 2 - 1) / 2 := by
          rw [← hpq]
          exact card_psl2_sq hpJ hpodd
        have hm16 : q ^ 2 * ((q ^ 2) ^ 2 - 1) / 2 % 16 = 8 :=
          mod_sixteen_L2 (sq_sq_mod_of_mod_eight hq8)
        rw [hJc]
        intro h64
        omega
      · have := card_alt5 h8a
        omega
    ·
      rcases h9 with ⟨s, p, hp, hp3, hpB, hJ⟩ | ⟨h9a, -⟩ | ⟨h9a, -⟩
      · haveI := Fact.mk hp
        have hp2 : p ≠ 2 := by omega
        have hpq : p = q := sl2_quot_eq (by omega) hp2 hpB hB hq hq2
        subst hpq
        rcases hJ with hJ | hJ
        · exact not64_pslEps3 hq8 s hJ
        · exact not64_slEps3 hq hq8 s hJ
      · have := card_alt6 h9a
        omega
      · have hc := card_hat h9a
        rw [card_alternatingGroup_six] at hc
        have h1080 : q * (q ^ 2 - 1) / 2 * 2 ^ j = 1080 := by rw [← hcB, hc]
        obtain ⟨-, hNeq⟩ := pow2_eq_of_small hN660 h1080 (by norm_num)
        omega
    ·
      obtain ⟨p, hp, hp3, hext, -⟩ := h10
      haveI := Fact.mk hp
      obtain ⟨V, hVn, hPV, -, hcard⟩ := isExt_card_eq hext
      have hVc := card_elemAb hPV
      have hVodd : Odd (Nat.card ↥V) := by
        rw [hVc]
        exact Odd.pow (hp.odd_of_ne_two (by omega))
      have hVbot := odd_normal_eq_bot hS hEven V hVodd
      rw [hVbot, Subgroup.card_bot] at hVc
      have := hp.two_le
      nlinarith
    ·
      obtain ⟨h11a, -⟩ := h11
      have := card_alt6 h11a
      omega
    ·
      rcases h12 with ⟨h12a, -⟩ | ⟨h12a, -⟩
      · rcases h12a with h | h
        · obtain ⟨V, hVn, -, hPY, -⟩ := isExt_card_eq h
          exact (B2_dich_false hS hN8 hN660 hj hcQ (card_alt5 hPY) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)).elim
        · obtain ⟨V, hVn, -, hPY, -⟩ := isExt_card_eq h
          exact (B2_dich_false hS hN8 hN660 hj hcQ (card_alt6 hPY) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)).elim
      · rcases h12a with h | h
        · obtain ⟨V, hVn, -, hPY, -⟩ := isExt_card_eq h
          exact (B2_dich_false hS hN8 hN660 hj hcQ (card_alt5 hPY) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)).elim
        · obtain ⟨V, hVn, -, hPY, -⟩ := isExt_card_eq h
          have hc := card_hat hPY
          rw [card_alternatingGroup_six] at hc
          exact (B2_dich_false hS hN8 hN660 hj hcQ hc (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)).elim
    ·
      obtain ⟨h13a, -⟩ := h13
      rcases h13a with h | h | h | h | h | h | h
      ·
        have hM := card_M22 h
        have hqm : q ∣ 2 ^ 7 * 3 ^ 2 * 5 ^ 1 * 7 ^ 1 * 11 := by
          have e : (443520 : ℕ) = 2 ^ 7 * 3 ^ 2 * 5 ^ 1 * 7 ^ 1 * 11 := by norm_num
          rw [← e, ← hM]
          exact hqB
        have hq11' := dvd_eleven_of_smooth hq hq11 hqm
        have hN660' : q * (q ^ 2 - 1) / 2 = 660 := by
          subst hq11'
          norm_num
        rw [hN660', hM] at hcB
        omega
      ·
        have hc := card_psl34 h
        have hqB' : q ∣ 20160 := by
          rw [← hc]
          exact hqB
        exact (not_dvd_smooth hq hq11 (show (20160 : ℕ) = 2 ^ 6 * 3 ^ 2 * 5 ^ 1 * 7 ^ 1 by norm_num)
          hqB').elim
      ·
        obtain ⟨V, hVn, -, hPY, -⟩ := isExt_card_eq h
        have hY := card_alt7 hPY
        have hNc := N_dvd_of_quot hS hcQ hj hY (by norm_num)
        exact (not_dvd_2520 hq hq11 (dvd_trans hqN hNc)).elim
      · obtain ⟨V, hVn, -, hPY, -⟩ := isExt_card_eq h
        exact (B2_dich_false hS hN8 hN660 hj hcQ (card_psl32 hPY) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)).elim
      · obtain ⟨V, hVn, -, hPY, -⟩ := isExt_card_eq h
        exact (B2_dich_false hS hN8 hN660 hj hcQ (card_psl32 hPY) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)).elim
      · obtain ⟨V, hVn, -, hPY, -⟩ := isExt_card_eq h
        exact (B2_dich_false hS hN8 hN660 hj hcQ (card_alt6 hPY) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)).elim
      · obtain ⟨V, hVn, -, hPY, -⟩ := isExt_card_eq h
        exact (B2_dich_false hS hN8 hN660 hj hcQ (card_alt5 hPY) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)).elim
    ·
      obtain ⟨h14a, -⟩ := h14
      rcases h14a with h | h | h | h
      ·
        obtain ⟨V, hVn, -, hPY, -⟩ := isExt_card_eq h
        have hY := card_psl42 hPY
        have hNc := N_dvd_of_quot hS hcQ hj hY (by norm_num)
        exact (not_dvd_smooth hq hq11 (show (20160 : ℕ) = 2 ^ 6 * 3 ^ 2 * 5 ^ 1 * 7 ^ 1 by norm_num)
          (dvd_trans hqN hNc)).elim
      · obtain ⟨V, hVn, -, hPY, -⟩ := isExt_card_eq h
        exact (B2_dich_false hS hN8 hN660 hj hcQ (card_psl32 hPY) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)).elim
      · obtain ⟨V, hVn, -, hPY, -⟩ := isExt_card_eq h
        exact (B2_dich_false hS hN8 hN660 hj hcQ (card_psl32 hPY) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)).elim
      · obtain ⟨V, hVn, -, hPY, -⟩ := isExt_card_eq h
        have hc := card_hat hPY
        rw [card_alternatingGroup_six] at hc
        exact (B2_dich_false hS hN8 hN660 hj hcQ hc (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)).elim
    ·
      obtain ⟨h15a, -⟩ := h15
      have := card_alt5 h15a
      omega
    ·
      obtain ⟨h16a, -⟩ := h16
      obtain ⟨V, hVn, -, hPY, -⟩ := isExt_card_eq h16a
      exact (B2_dich_false hS hN8 hN660 hj hcQ (card_alt5 hPY) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)).elim
    ·
      obtain ⟨-, h17b⟩ := h17
      rcases h17b with h | h | h | h | h | h
      ·
        obtain ⟨V, hVn, -, hPY, hcard⟩ := isExt_card_eq h
        have hY := card_hat hPY
        have hMc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = 443520 :=
          CFSG.Sporadic.Mathieu.card_M22
        rw [hMc] at hY
        have hNc := N_dvd_of_quot hS hcQ hj hY (by norm_num)
        have hqc : q ∣ 2 ^ 7 * 3 ^ 3 * 5 ^ 1 * 7 ^ 1 * 11 := by
          have e : (3 * 443520 : ℕ) = 2 ^ 7 * 3 ^ 3 * 5 ^ 1 * 7 ^ 1 * 11 := by norm_num
          rw [← e]
          exact dvd_trans hqN hNc
        have hq11' := dvd_eleven_of_smooth hq hq11 hqc
        have hN660' : q * (q ^ 2 - 1) / 2 = 660 := by
          subst hq11'
          norm_num
        rw [hN660'] at hcB
        have hBV := hcard
        rw [hY] at hBV
        omega
      ·
        obtain ⟨V, hVn, -, hPY, hcard⟩ := isExt_card_eq h
        have hY := card_isSporadic_M24 hPY
        have hNc := N_dvd_of_quot hS hcQ hj hY (by norm_num)
        have hqc : q ∣ 2 ^ 10 * 3 ^ 3 * 5 ^ 1 * 7 ^ 1 * 11 * 23 := by
          have e : (244823040 : ℕ) = 2 ^ 10 * 3 ^ 3 * 5 ^ 1 * 7 ^ 1 * 11 * 23 := by norm_num
          rw [← e]
          exact dvd_trans hqN hNc
        rcases dvd_eleven_or_23 hq hq11 hqc with hq11' | hq23
        · have hN660' : q * (q ^ 2 - 1) / 2 = 660 := by
            subst hq11'
            norm_num
          rw [hN660'] at hcB
          have hBV := hcard
          rw [hY] at hBV
          omega
        · omega
      ·
        have hc := card_alt5 h
        rw [hcQ] at hc
        omega
      ·
        have hc := card_hat h
        rw [card_alternatingGroup_six, hcQ] at hc
        omega
      ·
        have hc := card_psl42 h
        rw [hcQ] at hc
        omega
      ·
        have hc := card_psl32 h
        rw [hcQ] at hc
        omega
    ·
      obtain ⟨h18a, -⟩ := h18
      rcases h18a with h | h
      · obtain ⟨V, hVn, -, hPY, -⟩ := isExt_card_eq h
        exact (B2_dich_false hS hN8 hN660 hj hcQ (card_alt5 hPY) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)).elim
      · obtain ⟨V, hVn, -, hPY, -⟩ := isExt_card_eq h
        exact (B2_dich_false hS hN8 hN660 hj hcQ (card_psl32 hPY) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)).elim
    ·
      obtain ⟨h19a, -⟩ := h19
      rcases h19a with h | h
      · obtain ⟨V, hVn, -, hPY, -⟩ := isExt_card_eq h
        exact (B2_dich_false hS hN8 hN660 hj hcQ (card_psl32 hPY) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)).elim
      · obtain ⟨V, hVn, -, hPY, -⟩ := isExt_card_eq h
        have hc := card_hat hPY
        rw [card_alternatingGroup_six] at hc
        exact (B2_dich_false hS hN8 hN660 hj hcQ hc (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)).elim
    ·
      obtain ⟨h20a, -⟩ := h20
      rcases h20a with h | h
      · have hc := card_alt5 h
        rw [hcQ] at hc
        omega
      · have hc := card_psl32 h
        rw [hcQ] at hc
        omega
  ·
    right
    dsimp only [A312Nonquasi] at h
    set OL : Subgroup Q := (CFSG.oddCore ↥J).map J.subtype with hOL
    have hBN : B ≤ Subgroup.normalizer (OL : Set Q) := le_normalizer_oddCore hBJ
    rcases h with ⟨-, hJ, p, hp, hp2, hSL⟩ | ⟨-, -, N, hNn, hNeq, hSL5⟩
    ·
      have hc := card_quot_oddCore_eq_of_sup hBJ hS hEven hJ.le
      have hsl := card_sl2 hp hSL
      obtain ⟨eB⟩ := equiv_quot_oddCore_of_sup hBJ hS hEven hJ.le
      obtain ⟨eJ⟩ := hSL
      haveI : Fact p.Prime := ⟨hp⟩
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      have hp4 : 4 ≤ p := by
        rcases (show p = 3 ∨ 4 ≤ p by omega) with rfl | h4
        · norm_num at hsl
          omega
        · exact h4
      have hO2 : Nat.card (CFSG.pCore 2 ↥B) = 2 :=
        sl2_O2_card p hp2 hp4 (eB.trans eJ) hS (by omega)
      have hJx : Nat.card ↥J = q * (q ^ 2 - 1) / 2 * 2 * Nat.card (CFSG.oddCore ↥J) := by
        rw [card_eq_quot_mul_oddCore ↥J, hc, card_eq_quot_mul B, hcQ, hO2]
      exact not64_of_two_N (oddCore_odd ↥J) hN8 hJx
    ·
      subst hNeq
      obtain ⟨γ, hγdef⟩ : ∃ γ : ↥B →* ↥(B ⊔ OL) ⧸ OL.subgroupOf (B ⊔ OL),
          γ = (QuotientGroup.mk' (OL.subgroupOf (B ⊔ OL))).comp
            (Subgroup.inclusion (le_sup_left : B ≤ B ⊔ OL)) := ⟨_, rfl⟩
      have hγ : Function.Surjective γ := by
        rw [hγdef]
        exact surj_of_cover (le_sup_left : B ≤ B ⊔ OL) (OL.subgroupOf (B ⊔ OL))
          (cover_of_sup (le_sup_left : B ≤ B ⊔ OL) OL hBN le_rfl (OL.subgroupOf (B ⊔ OL))
            (fun o ho hol => ⟨⟨o, hol⟩, Subgroup.mem_subgroupOf.mpr ho, rfl⟩))
      have h120 : Nat.card (↥B ⧸ γ.ker) = 120 := by
        have h2 := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective γ hγ).toEquiv
        rw [h2, card_sl2 (by norm_num : Nat.Prime 5) hSL5] <;> norm_num
      exact (B2_dich_false hS hN8 hN660 hj hcQ h120 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)).elim

end CFSG.Quasithin.H13.NF314ptA312
