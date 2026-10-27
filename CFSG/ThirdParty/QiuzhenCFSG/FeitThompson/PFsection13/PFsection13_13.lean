module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection13.PFsection13_12
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_7

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 13: PFsection13_13
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section13

universe v
universe u

/-! ## (13.13) -/


private theorem section13_three_le_of_odd_prime_for_13_13 {n : ℕ}
    (hn : Nat.Prime n) (hodd : Odd n) :
    3 ≤ n := by
  have h2le : 2 ≤ n := hn.two_le
  have hn_ne_two : n ≠ 2 := by
    intro hn2
    have hnot_even : ¬ Even n := Nat.not_even_iff_odd.mpr hodd
    exact hnot_even (by rw [hn2]; exact even_two)
  omega

private theorem section13_five_le_of_prime_three_le_ne_three_for_13_13 {n : ℕ}
    (hn : Nat.Prime n) (h3 : 3 ≤ n) (hne3 : n ≠ 3) :
    5 ≤ n := by
  by_contra hnot
  have hn_le4 : n ≤ 4 := by omega
  interval_cases n
  · exact hne3 rfl
  · have h2dvd : 2 ∣ 4 := by norm_num
    have h2eq := hn.eq_one_or_self_of_dvd 2 h2dvd
    omega

private theorem section13_p_sub_one_pow_lt_geom_quotient_for_13_13
    {p q : ℕ} (hp : Nat.Prime p) (hq1 : 1 < q) :
    (p - 1) ^ (q - 1) < (p ^ q - 1) / (p - 1) := by
  rw [← Nat.geomSum_eq hp.two_le q]
  have hmem : q - 1 ∈ Finset.range q := by
    simp
    omega
  have hterm_sum : p ^ (q - 1) ≤ ∑ i ∈ Finset.range q, p ^ i := by
    exact Finset.single_le_sum (by
      intro _ _
      exact Nat.zero_le _) hmem
  have hexp_ne : q - 1 ≠ 0 := by omega
  have hp2 : 2 ≤ p := hp.two_le
  have hbase_lt : p - 1 < p := by omega
  have hstrict : (p - 1) ^ (q - 1) < p ^ (q - 1) :=
    Nat.pow_lt_pow_left hbase_lt hexp_ne
  exact hstrict.trans_le hterm_sum

private theorem section13_odd_dvd_even_pow_div_two_pow_for_13_13
    {u b e : ℕ} (huOdd : Odd u) (hdiv : u ∣ (2 * b) ^ e) :
    u ∣ b ^ e := by
  have hcop : Nat.Coprime u (2 ^ e) :=
    (Odd.coprime_two_right huOdd).pow_right e
  have hdiv' : u ∣ 2 ^ e * b ^ e := by
    simpa [mul_pow] using hdiv
  exact hcop.dvd_of_dvd_mul_left hdiv'

private theorem section13_ten_mul_lt_seven_mul_two_pow_pred_for_13_13
    {q : ℕ} (hq5 : 5 ≤ q) :
    10 * q < 7 * 2 ^ (q - 1) := by
  have haux : ∀ k : ℕ, 10 * (5 + k) < 7 * 2 ^ (4 + k) := by
    intro k
    induction k with
    | zero =>
        norm_num
    | succ k ih =>
        rw [show 4 + (k + 1) = (4 + k) + 1 by omega, pow_succ]
        calc
          10 * (5 + (k + 1)) < 2 * (10 * (5 + k)) := by omega
          _ < 2 * (7 * 2 ^ (4 + k)) :=
            (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).2 ih
          _ = 7 * (2 ^ (4 + k) * 2) := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hq5
  simpa [show 5 + k - 1 = 4 + k by omega] using haux k

private theorem section13_q_div_two_pow_lt_seven_tenths_for_13_13
    {q : ℕ} (hq5 : 5 ≤ q) :
    (q : ℝ) / (2 : ℝ) ^ (q - 1) < (7 : ℝ) / 10 := by
  have hnat : 10 * q < 7 * 2 ^ (q - 1) :=
    section13_ten_mul_lt_seven_mul_two_pow_pred_for_13_13 hq5
  have hreal : (10 : ℝ) * (q : ℝ) < 7 * ((2 : ℝ) ^ (q - 1)) := by
    exact_mod_cast hnat
  have hden : (0 : ℝ) < (2 : ℝ) ^ (q - 1) := by positivity
  field_simp [hden.ne']
  nlinarith

private theorem section13_m_lt_q_div_two_pow_of_u_half_bound_for_13_13
    {p q u c : ℕ} {m : ℝ}
    (hp : Nat.Prime p) (hqpos : 0 < q) (hq1 : 1 < q) (hc1 : c = 1)
    (h10ineq : (u : ℝ) / (c : ℝ) > (m * (p : ℝ) ^ (q - 1)) / (q : ℝ))
    (huBound : u ≤ ((p - 1) / 2) ^ (q - 1)) :
    m < (q : ℝ) / (2 : ℝ) ^ (q - 1) := by
  let e := q - 1
  have he_ne : e ≠ 0 := by dsimp [e]; omega
  have hp_pos_nat : 0 < p := hp.pos
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_pos_nat
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast hqpos
  have htwoPow : (0 : ℝ) < (2 : ℝ) ^ e := by positivity
  have hpPow : (0 : ℝ) < (p : ℝ) ^ e := pow_pos hp_pos e
  have hb_lt : ((((p - 1) / 2 : ℕ) : ℝ) < (p : ℝ) / 2) := by
    have hp2 : 2 ≤ p := hp.two_le
    have hp1 : 1 ≤ p := by omega
    have hb_le :
        (((p - 1) / 2 : ℕ) : ℝ) ≤ (((p - 1 : ℕ) : ℝ) / (2 : ℝ)) :=
      Nat.cast_div_le
    rw [Nat.cast_sub hp1] at hb_le
    have hlt : (((p : ℝ) - (1 : ℝ)) / 2) < (p : ℝ) / 2 := by nlinarith
    exact lt_of_le_of_lt hb_le (by simpa using hlt)
  have hb_nonneg : (0 : ℝ) ≤ (((p - 1) / 2 : ℕ) : ℝ) := by positivity
  have hpow_lt : ((((p - 1) / 2 : ℕ) : ℝ) ^ e) < ((p : ℝ) / 2) ^ e :=
    pow_lt_pow_left₀ hb_lt hb_nonneg he_ne
  have hu_le_half : (u : ℝ) ≤ ((((p - 1) / 2 : ℕ) : ℝ) ^ (q - 1)) := by
    exact_mod_cast huBound
  have hu_lt : (u : ℝ) < (p : ℝ) ^ e / (2 : ℝ) ^ e := by
    have hpow_lt' :
        ((((p - 1) / 2 : ℕ) : ℝ) ^ e) < (p : ℝ) ^ e / (2 : ℝ) ^ e := by
      simpa [div_pow] using hpow_lt
    dsimp [e] at hpow_lt' ⊢
    exact lt_of_le_of_lt hu_le_half hpow_lt'
  have hmp_lt_u : (m * (p : ℝ) ^ e) / (q : ℝ) < (u : ℝ) := by
    dsimp [e]
    simpa [hc1] using h10ineq
  have hmp_lt :
      (m * (p : ℝ) ^ e) / (q : ℝ) < (p : ℝ) ^ e / (2 : ℝ) ^ e :=
    lt_trans hmp_lt_u hu_lt
  have hscale_pos : 0 < (q : ℝ) / (p : ℝ) ^ e := div_pos hq_pos hpPow
  have hscaled := mul_lt_mul_of_pos_right hmp_lt hscale_pos
  calc
    m = ((m * (p : ℝ) ^ e) / (q : ℝ)) * ((q : ℝ) / (p : ℝ) ^ e) := by
      field_simp [hq_pos.ne', hpPow.ne']
    _ < ((p : ℝ) ^ e / (2 : ℝ) ^ e) * ((q : ℝ) / (p : ℝ) ^ e) := hscaled
    _ = (q : ℝ) / (2 : ℝ) ^ e := by
      field_simp [hpPow.ne', htwoPow.ne']

private theorem section13_le_half_of_proper_dvd_for_13_13
    {u N : ℕ} (hNpos : 0 < N) (hdiv : u ∣ N) (hne : u ≠ N) :
    (u : ℝ) ≤ (N : ℝ) / 2 := by
  rcases hdiv with ⟨k, hk⟩
  have hkpos : 0 < k := by
    by_contra hnot
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hk0, Nat.mul_zero] at hk
    omega
  have hkne1 : k ≠ 1 := by
    intro hk1
    apply hne
    rw [hk, hk1, Nat.mul_one]
  have hk2 : 2 ≤ k := by omega
  have hleNat : 2 * u ≤ N := by
    rw [hk]
    calc
      2 * u = u * 2 := by omega
      _ ≤ u * k := Nat.mul_le_mul_left u hk2
  have hleR : (2 : ℝ) * (u : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hleNat
  nlinarith

private theorem section13_half_square_bound_for_13_13
    {p : ℕ} (hp1 : 1 ≤ p) :
    (((p - 1 : ℕ) : ℝ) ^ 2) / 8 ≤ ((p : ℝ) ^ 2 - 1) / 6 := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp1
  rw [Nat.cast_sub hp1]
  nlinarith [sq_nonneg ((p : ℝ) - 1)]

private theorem section13_primes_ne_of_sourceContext_for_13_13
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hqPrime : Nat.Prime q) :
    p ≠ q := by
  rcases hsource with
    ⟨hcase, _hptypeS, _hptypeT, hp_card, hq_card, _hC, _hD, _hc_card,
      _hd_card, _hU_card, _hV_card, _hSfam, _hTfam, _hDadeS, _hDadeT,
      _hnotationData⟩
  rcases hcase with
    ⟨hprod, hWcyc, _hW1ne, _hW2ne, _hnorm, _hSmax, _hTmax, _hSF, _hTF,
      _hSeq, _hTeq, _hSdisj, _hTdisj, _hST, _hTypeII, _hSType, _hTType,
      _hCover⟩
  have hcop_cards : Nat.Coprime (Nat.card W1) (Nat.card W2) :=
    section13_natCard_coprime_of_section12InternalDirectProduct_cyclic hprod hWcyc
  have hcop_qp : Nat.Coprime q p := by
    simpa [hq_card, hp_card] using hcop_cards
  intro hpq
  have hcop_qq : Nat.Coprime q q := by
    simpa [hpq] using hcop_qp
  exact hqPrime.ne_one (Nat.Coprime.eq_one_of_dvd hcop_qq dvd_rfl)

public theorem theorem_13_13
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      case_9_7_a_sourceDataForSection13 Smax P U W1 W2 C p q u →
        q = 3 ∧ u = (p - 1) ^ 2 / 4 := by
  intro hsource hcaseA
  rcases hcaseA with ⟨hBarU, a, hcaseA97⟩
  have hpPrime : Nat.Prime p := Section9.case_9_7_a_p_prime_sec9 hcaseA97
  have hqPrime : Nat.Prime q := Section9.case_9_7_a_q_prime_sec9 hcaseA97
  have hp_card : p = Nat.card W2 := by
    rcases hsource with ⟨_hcaseB, _hptypeS, _hptypeT, hp_card, _hrest⟩
    exact hp_card
  have hq_card : q = Nat.card W1 := by
    rcases hsource with
      ⟨_hcaseB, _hptypeS, _hptypeT, _hp_card, hq_card, _hrest⟩
    exact hq_card
  have hMin : IsMinCE G :=
    section13_theorem_13_2_global_isMinCE_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource
  have hoddG : Odd (Nat.card G) := hMin.odd_order
  have hpOdd : Odd p := by
    rw [hp_card]
    exact section13_odd_card_subgroup_of_odd_group W2 hoddG
  have hqOdd : Odd q := by
    rw [hq_card]
    exact section13_odd_card_subgroup_of_odd_group W1 hoddG
  have hp3 : 3 ≤ p :=
    section13_three_le_of_odd_prime_for_13_13 hpPrime hpOdd
  have hq3le : 3 ≤ q :=
    section13_three_le_of_odd_prime_for_13_13 hqPrime hqOdd
  have hp_ne_two : p ≠ 2 := by
    intro hp2
    have hnot_even : ¬ Even p := Nat.not_even_iff_odd.mpr hpOdd
    exact hnot_even (by rw [hp2]; exact even_two)
  have hdivPow : u ∣ (p - 1) ^ (q - 1) :=
    Section9.theorem_9_7_case_a_barU_card_dvd_p_minus_one_pow_sec9
      Smax P U W1 W2 ⊥ C p q a u hcaseA97 hBarU
  have h10 : theorem_13_10_hypothesis Smax P C Sfam p q u := by
    by_contra hnot10
    have h3 := theorem_13_3 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hsource
    rcases h3.2 hnot10 with ⟨_hCbot, _hcaseB, huGeom⟩
    have hpow_pos : 0 < (p - 1) ^ (q - 1) := by
      have hp_sub_pos : 0 < p - 1 := Nat.sub_pos_of_lt hpPrime.one_lt
      exact pow_pos hp_sub_pos (q - 1)
    have hu_le_pow : u ≤ (p - 1) ^ (q - 1) :=
      Nat.le_of_dvd hpow_pos hdivPow
    have hgeom_le_pow : (p ^ q - 1) / (p - 1) ≤ (p - 1) ^ (q - 1) := by
      simpa [huGeom] using hu_le_pow
    have hlt :
        (p - 1) ^ (q - 1) < (p ^ q - 1) / (p - 1) :=
      section13_p_sub_one_pow_lt_geom_quotient_for_13_13 hpPrime hqPrime.one_lt
    exact (not_lt_of_ge hgeom_le_pow) hlt
  have hc1 : c = 1 :=
    theorem_13_12 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hsource
  have hUodd : Odd (Nat.card U) :=
    section13_odd_card_subgroup_of_odd_group U hoddG
  have huOdd : Odd u := by
    rcases hBarU with ⟨_hCU, hnormal, hcard⟩
    letI : (C.subgroupOf U).Normal := hnormal
    have hquot_dvd : Nat.card (U ⧸ C.subgroupOf U) ∣ Nat.card U :=
      Subgroup.card_quotient_dvd_card (C.subgroupOf U)
    have hquot_odd : Odd (Nat.card (U ⧸ C.subgroupOf U)) :=
      Odd.of_dvd_nat hUodd hquot_dvd
    simpa [← hcard] using hquot_odd
  have hp_even_sub_one : Even (p - 1) :=
    hpPrime.even_sub_one hp_ne_two
  have htwo_dvd_p_sub_one : 2 ∣ p - 1 :=
    even_iff_two_dvd.mp hp_even_sub_one
  have hp_sub_one_eq_two_mul : p - 1 = 2 * ((p - 1) / 2) := by
    have h := Nat.div_mul_cancel htwo_dvd_p_sub_one
    rw [mul_comm] at h
    exact h.symm
  have hdivHalfPow : u ∣ ((p - 1) / 2) ^ (q - 1) := by
    have hdivEven : u ∣ (2 * ((p - 1) / 2)) ^ (q - 1) := by
      rw [← hp_sub_one_eq_two_mul]
      exact hdivPow
    exact section13_odd_dvd_even_pow_div_two_pow_for_13_13 huOdd hdivEven
  have hhalf_pos : 0 < (p - 1) / 2 := by omega
  have huHalfBound : u ≤ ((p - 1) / 2) ^ (q - 1) :=
    Nat.le_of_dvd (pow_pos hhalf_pos (q - 1)) hdivHalfPow
  let m : ℝ :=
    1 - 1 / ((q - 1 : ℕ) : ℝ) - ((q - 1 : ℕ) : ℝ) / ((q : ℝ) ^ p) +
      1 / (((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ p))
  have h10ineq := theorem_13_10 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d m hsource h10 rfl
  have h11 := theorem_13_11 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d m hsource h10 rfl
  have hq_eq_three : q = 3 := by
    by_contra hq_ne_three
    have hq5 : 5 ≤ q :=
      section13_five_le_of_prime_three_le_ne_three_for_13_13
        hqPrime hq3le hq_ne_three
    have hm_upper : m < (q : ℝ) / (2 : ℝ) ^ (q - 1) :=
      section13_m_lt_q_div_two_pow_of_u_half_bound_for_13_13
        hpPrime hqPrime.pos hqPrime.one_lt hc1 h10ineq huHalfBound
    have hm_lt_seven : m < (7 : ℝ) / 10 :=
      lt_trans hm_upper (section13_q_div_two_pow_lt_seven_tenths_for_13_13 hq5)
    have hm_gt_seven : (7 : ℝ) / 10 < m := h11.2.1 hp3 hq5
    linarith
  have hp_ne_q : p ≠ q :=
    section13_primes_ne_of_sourceContext_for_13_13
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource hqPrime
  have hp_ne_three : p ≠ 3 := by
    intro hp_eq_three
    exact hp_ne_q (by rw [hp_eq_three, hq_eq_three])
  have hp5 : 5 ≤ p :=
    section13_five_le_of_prime_three_le_ne_three_for_13_13
      hpPrime hp3 hp_ne_three
  have hdivTarget : u ∣ (p - 1) ^ 2 / 4 := by
    have hdivHalfSq : u ∣ ((p - 1) / 2) ^ 2 := by
      simpa [hq_eq_three] using hdivHalfPow
    have hhalfSq :
        ((p - 1) / 2) ^ 2 = (p - 1) ^ 2 / 4 := by
      simpa using
        (Nat.div_pow (a := 2) (b := p - 1) (c := 2) htwo_dvd_p_sub_one)
    simpa [hhalfSq] using hdivHalfSq
  by_cases hu_eq_target : u = (p - 1) ^ 2 / 4
  · exact ⟨hq_eq_three, hu_eq_target⟩
  · have hhalfSq :
        ((p - 1) / 2) ^ 2 = (p - 1) ^ 2 / 4 := by
      simpa using
        (Nat.div_pow (a := 2) (b := p - 1) (c := 2) htwo_dvd_p_sub_one)
    have htarget_pos : 0 < (p - 1) ^ 2 / 4 := by
      rw [← hhalfSq]
      exact pow_pos hhalf_pos 2
    have hu_le_target_half :
        (u : ℝ) ≤ (((p - 1) ^ 2 / 4 : ℕ) : ℝ) / 2 :=
      section13_le_half_of_proper_dvd_for_13_13 htarget_pos hdivTarget hu_eq_target
    have htarget_cast_le :
        (((p - 1) ^ 2 / 4 : ℕ) : ℝ) ≤ (((p - 1 : ℕ) : ℝ) ^ 2) / 4 := by
      have hcast :
          (((p - 1) ^ 2 / 4 : ℕ) : ℝ) ≤ (((p - 1) ^ 2 : ℕ) : ℝ) / (4 : ℝ) :=
        Nat.cast_div_le
      simpa [Nat.cast_pow] using hcast
    have hu_upper : (u : ℝ) ≤ (((p - 1 : ℕ) : ℝ) ^ 2) / 8 := by
      calc
        (u : ℝ) ≤ (((p - 1) ^ 2 / 4 : ℕ) : ℝ) / 2 := hu_le_target_half
        _ ≤ ((((p - 1 : ℕ) : ℝ) ^ 2) / 4) / 2 := by
          exact div_le_div_of_nonneg_right htarget_cast_le (by norm_num : (0 : ℝ) ≤ 2)
        _ = (((p - 1 : ℕ) : ℝ) ^ 2) / 8 := by ring
    have hlower : ((p : ℝ) ^ 2 - 1) / 6 < (u : ℝ) := by
      have h11c := h11.2.2 hp5 hq_eq_three
      simpa [hc1] using h11c.2
    have hhalf_bound :
        (((p - 1 : ℕ) : ℝ) ^ 2) / 8 ≤ ((p : ℝ) ^ 2 - 1) / 6 :=
      section13_half_square_bound_for_13_13 (by omega : 1 ≤ p)
    linarith

public theorem theorem_13_13_case_9_7_b_sourceData_of_q_ne_three
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hq_ne_three : q ≠ 3) :
    case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u := by
  rcases theorem_13_2_case_9_7_sourceData_of_sourceContext
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d hsource with hcaseA | hcaseB
  · have h13 := theorem_13_13 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hsource hcaseA
    exact False.elim (hq_ne_three h13.1)
  · exact hcaseB
end CFSG.Section13
