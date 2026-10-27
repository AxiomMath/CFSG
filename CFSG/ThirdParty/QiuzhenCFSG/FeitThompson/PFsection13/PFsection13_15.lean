module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection13.PFsection13_14

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 13: PFsection13_15
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section13

universe v
universe u

/-! ## (13.15) -/


private theorem section13_15_primes_odd_ne
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcaseB : case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u) :
    Nat.Prime p ∧ Nat.Prime q ∧ Odd p ∧ Odd q ∧ p ≠ q ∧ 3 ≤ p ∧ 3 ≤ q := by
  have hpPrime : Nat.Prime p := Section9.case_9_7_b_p_prime_sec9 hcaseB
  have hqPrime : Nat.Prime q := Section9.case_9_7_b_q_prime_sec9 hcaseB
  have hp_card : p = Nat.card W2 := by
    rcases hsource with ⟨_hcase, _hptypeS, _hptypeT, hp_card, _hrest⟩
    exact hp_card
  have hq_card : q = Nat.card W1 := by
    rcases hsource with
      ⟨_hcase, _hptypeS, _hptypeT, _hp_card, hq_card, _hrest⟩
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
  have hp_ne_q : p ≠ q := by
    rcases hsource with
      ⟨hcase, _hptypeS, _hptypeT, hp_card, hq_card, _hrest⟩
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
  have hp3 : 3 ≤ p := by
    have h2le := hpPrime.two_le
    have hp_ne_two : p ≠ 2 := by
      intro hp2
      exact (Nat.not_even_iff_odd.mpr hpOdd) (by rw [hp2]; exact even_two)
    omega
  have hq3 : 3 ≤ q := by
    have h2le := hqPrime.two_le
    have hq_ne_two : q ≠ 2 := by
      intro hq2
      exact (Nat.not_even_iff_odd.mpr hqOdd) (by rw [hq2]; exact even_two)
    omega
  exact ⟨hpPrime, hqPrime, hpOdd, hqOdd, hp_ne_q, hp3, hq3⟩

private theorem section13_15_u_le_div_of_factor_ge
    {N u b L : ℕ} (hN : N = b * u) (hLpos : 0 < L) (hLb : L ≤ b) :
    (u : ℝ) ≤ (N : ℝ) / (L : ℝ) := by
  have hmul_le : L * u ≤ N := by
    rw [hN]
    exact Nat.mul_le_mul_right u hLb
  have hmul_le_R : (L : ℝ) * (u : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hmul_le
  have hLposR : (0 : ℝ) < L := by exact_mod_cast hLpos
  exact (le_div_iff₀ hLposR).mpr (by simpa [mul_comm] using hmul_le_R)

private theorem section13_15_geom_three_cast
    {p : ℕ} (hp1 : 1 < p) :
    (((p ^ 3 - 1) / (p - 1) : ℕ) : ℝ) = (p : ℝ) ^ 2 + (p : ℝ) + 1 := by
  have hp2 : 2 ≤ p := by omega
  rw [← Nat.geomSum_eq hp2 3]
  norm_num [Finset.sum_range_succ]
  ring

private theorem section13_15_factor_gt_two_mul_q_contradiction
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d b : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcaseB : case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (h10 : theorem_13_10_hypothesis Smax P C Sfam p q u)
    (hN : (p ^ q - 1) / (p - 1) = b * u)
    (hbgt : 2 * q < b) :
    False := by
  rcases section13_15_primes_odd_ne Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hsource hcaseB with
    ⟨hpPrime, hqPrime, _hpOdd, _hqOdd, hp_ne_q, hp3, hq3⟩
  have hc1 : c = 1 :=
    theorem_13_12 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hsource
  let m : ℝ :=
    1 - 1 / ((q - 1 : ℕ) : ℝ) - ((q - 1 : ℕ) : ℝ) / ((q : ℝ) ^ p) +
      1 / (((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ p))
  have hm :
      m = 1 - 1 / ((q - 1 : ℕ) : ℝ) - ((q - 1 : ℕ) : ℝ) / ((q : ℝ) ^ p) +
        1 / (((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ p)) := rfl
  have h10ineq : (u : ℝ) / (c : ℝ) > (m * (p : ℝ) ^ (q - 1)) / (q : ℝ) :=
    theorem_13_10 Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d m hsource h10 hm
  have h11 :=
    theorem_13_11 Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d m hsource h10 hm
  have hp_pos : 0 < p := hpPrime.pos
  have hq_pos : 0 < q := hqPrime.pos
  have hp_one : 1 < p := hpPrime.one_lt
  have hgeom_cast :
      ((((p ^ q - 1) / (p - 1) : ℕ) : ℝ)) =
        ((p : ℝ) ^ q - 1) / ((p - 1 : ℕ) : ℝ) :=
    section13_real_geom_quotient_cast (p := q) (q := p) hp_one
  have hbLower : 2 * q + 1 ≤ b := by omega
  have hu_le_nat :
      (u : ℝ) ≤ (((p ^ q - 1) / (p - 1) : ℕ) : ℝ) /
          ((2 * q + 1 : ℕ) : ℝ) :=
    section13_15_u_le_div_of_factor_ge hN (by positivity) hbLower
  have huc_le :
      (u : ℝ) / (c : ℝ) ≤
        (((p : ℝ) ^ q - 1) / ((p - 1 : ℕ) : ℝ)) /
          ((2 * q + 1 : ℕ) : ℝ) := by
    simpa [hc1, hgeom_cast] using hu_le_nat
  have hm_upper :
      m <
        ((((p : ℝ) ^ q - 1) / ((p - 1 : ℕ) : ℝ)) /
            ((2 * q + 1 : ℕ) : ℝ)) *
          (q : ℝ) / ((p : ℝ) ^ (q - 1)) :=
    section13_m_lt_of_u_div_c_le hp_pos hq_pos h10ineq huc_le
  have hm_qp :
      m < ((q : ℝ) * (p : ℝ)) /
        (((2 * q + 1 : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ)) :=
    lt_trans hm_upper (section13_m_upper_lt_qp_ratio hp_one hq_pos)
  by_cases hp_eq_three : p = 3
  · exact section13_numeric_contradiction_of_p_eq_three hqPrime hp_ne_q hq3
      h11.1 h11.2.1 hm_qp hp_eq_three
  · have hp5 : 5 ≤ p :=
      section13_five_le_of_prime_three_le_ne_three hpPrime hp3 hp_eq_three
    have hqeq : q = 3 :=
      section13_q_eq_three_of_five_le_numeric hqPrime hp5 hq3 h11.2.1 hm_qp
    have hu_lower : ((p : ℝ) ^ 2 - 1) / 6 < (u : ℝ) := by
      have h := (h11.2.2 hp5 hqeq).2
      simpa [hc1] using h
    have hb7 : 7 ≤ b := by omega
    have hN3 : (p ^ 3 - 1) / (p - 1) = b * u := by
      simpa [hqeq] using hN
    have hN3_cast :
        (b : ℝ) * (u : ℝ) = (p : ℝ) ^ 2 + (p : ℝ) + 1 := by
      have hcast : (((p ^ 3 - 1) / (p - 1) : ℕ) : ℝ) = (b : ℝ) * (u : ℝ) := by
        exact_mod_cast hN3
      have hgeom3 := section13_15_geom_three_cast (p := p) hp_one
      linarith
    have hterm_pos : 0 < (((p : ℝ) ^ 2 - 1) / 6) := by
      have hp5R : (5 : ℝ) ≤ p := by exact_mod_cast hp5
      nlinarith
    have hbposR : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
    have hbu_lower :
        (b : ℝ) * (((p : ℝ) ^ 2 - 1) / 6) < (b : ℝ) * (u : ℝ) :=
      mul_lt_mul_of_pos_left hu_lower hbposR
    have hseven_le_b : (7 : ℝ) ≤ b := by exact_mod_cast hb7
    have hseven_lower :
        (7 : ℝ) * (((p : ℝ) ^ 2 - 1) / 6) <
          (p : ℝ) ^ 2 + (p : ℝ) + 1 := by
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right hseven_le_b hterm_pos.le)
        (by simpa [hN3_cast] using hbu_lower)
    have hp_lt8 : p < 8 := by
      by_contra hnot
      have hp8R : (8 : ℝ) ≤ p := by exact_mod_cast (by omega : 8 ≤ p)
      nlinarith
    interval_cases p
    · have hu_ge_five : 5 ≤ u := by
        have hu_gt4_nat : 4 < u := by
          norm_num at hu_lower
          exact hu_lower
        omega
      have hN31 : 31 = b * u := by
        norm_num at hN3
        exact hN3
      have hbu_ge : 35 ≤ b * u := by
        exact Nat.mul_le_mul hb7 hu_ge_five
      omega
    · have h2dvd : 2 ∣ 6 := by norm_num
      have h2eq := hpPrime.eq_one_or_self_of_dvd 2 h2dvd
      omega
    · have hu_ge_nine : 9 ≤ u := by
        have hu_gt8_nat : 8 < u := by
          norm_num at hu_lower
          exact hu_lower
        omega
      have hN57 : 57 = b * u := by
        norm_num at hN3
        exact hN3
      have hbu_ge : 63 ≤ b * u := by
        exact Nat.mul_le_mul hb7 hu_ge_nine
      omega

private theorem section13_15_factor_le_two_mul_q
    {G : Type u} [Group G] [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d b : ℕ)
    (hsource : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcaseB : case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (hN : (p ^ q - 1) / (p - 1) = b * u) :
    b ≤ 2 * q := by
  rcases section13_15_primes_odd_ne Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hsource hcaseB with
    ⟨hpPrime, hqPrime, hpOdd, hqOdd, _hp_ne_q, _hp3, _hq3⟩
  have hNodd : Odd ((p ^ q - 1) / (p - 1)) :=
    (theorem_13_14 p q 1 hpPrime hqPrime hpOdd hqOdd).1
  by_cases h10 : theorem_13_10_hypothesis Smax P C Sfam p q u
  · by_contra hnot
    have hbgt : 2 * q < b := by omega
    exact section13_15_factor_gt_two_mul_q_contradiction
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d b hsource hcaseB h10 hN hbgt
  · have h3 := theorem_13_3 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hsource
    rcases h3.2 h10 with ⟨_hCbot, _hcaseB, huGeom⟩
    have hu_pos : 0 < u := by
      rw [huGeom]
      exact hNodd.pos
    have hb_eq_one : b = 1 := by
      have hmul : 1 * u = b * u := by
        simpa [huGeom] using hN
      exact (Nat.mul_right_cancel hu_pos hmul).symm
    rw [hb_eq_one]
    omega

private theorem section13_15_factor_eq_one_of_mod_ne
    {p q b u : ℕ}
    (hpPrime : Nat.Prime p) (hqPrime : Nat.Prime q) (hpOdd : Odd p) (hqOdd : Odd q)
    (hmod_ne : p % q ≠ 1)
    (hN : (p ^ q - 1) / (p - 1) = b * u)
    (hb_le : b ≤ 2 * q) :
    b = 1 := by
  have h14 := theorem_13_14 p q b hpPrime hqPrime hpOdd hqOdd
  have hNodd : Odd ((p ^ q - 1) / (p - 1)) := h14.1
  have hNodd' : Odd (b * u) := by
    rw [← hN]
    exact hNodd
  have hbOdd : Odd b := Nat.Odd.of_mul_left hNodd'
  have hbpos : 0 < b := hbOdd.pos
  have hb_dvd : b ∣ (p ^ q - 1) / (p - 1) := ⟨u, hN⟩
  have hbmod : b % q = 1 := (h14.2.2 hmod_ne).2 hbpos hb_dvd
  have hq_dvd_b_sub_one : q ∣ b - 1 := by
    have hbmodEq : b ≡ 1 [MOD q] := by
      rw [Nat.ModEq]
      have h1mod : 1 % q = 1 := Nat.mod_eq_of_lt hqPrime.one_lt
      simpa [h1mod] using hbmod
    exact (Nat.modEq_iff_dvd' (by omega : 1 ≤ b)).mp hbmodEq.symm
  rcases hq_dvd_b_sub_one with ⟨k, hk⟩
  have hb_eq : b = q * k + 1 := by
    omega
  have hk_le_one : k ≤ 1 := by
    by_contra hnot
    have hk2 : 2 ≤ k := by omega
    have hle : 2 * q + 1 ≤ q * k + 1 := by
      have hle' := Nat.add_le_add_right (Nat.mul_le_mul_left q hk2) 1
      simpa [Nat.mul_comm] using hle'
    omega
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · simpa [hk0] using hb_eq
  have hk1 : k = 1 := by omega
  have hb_eq_q_add_one : b = q + 1 := by
    simpa [hk1, Nat.mul_one] using hb_eq
  have hbEven : Even b := by
    rcases hqOdd with ⟨t, ht⟩
    rw [hb_eq_q_add_one, ht]
    exact ⟨t + 1, by omega⟩
  exact False.elim ((Nat.not_even_iff_odd.mpr hbOdd) hbEven)

private theorem section13_15_factor_eq_q_of_mod_eq
    {p q b u : ℕ}
    (hpPrime : Nat.Prime p) (hqPrime : Nat.Prime q) (hpOdd : Odd p) (hqOdd : Odd q)
    (hmod : p % q = 1)
    (hcop : Nat.Coprime u (p - 1))
    (hN : (p ^ q - 1) / (p - 1) = b * u)
    (hb_le : b ≤ 2 * q) :
    b = q := by
  have h14 := theorem_13_14 p q b hpPrime hqPrime hpOdd hqOdd
  have hNodd : Odd ((p ^ q - 1) / (p - 1)) := h14.1
  have hNodd' : Odd (b * u) := by
    rw [← hN]
    exact hNodd
  have hbOdd : Odd b := Nat.Odd.of_mul_left hNodd'
  have hq_dvd_N : q ∣ (p ^ q - 1) / (p - 1) := h14.2.1 hmod
  have hq_dvd_p_sub_one : q ∣ p - 1 := by
    have hpmod : p ≡ 1 [MOD q] := by
      rw [Nat.ModEq]
      have h1mod : 1 % q = 1 := Nat.mod_eq_of_lt hqPrime.one_lt
      simpa [h1mod] using hmod
    exact (Nat.modEq_iff_dvd' hpPrime.one_le).mp hpmod.symm
  have huq : Nat.Coprime u q :=
    Nat.Coprime.coprime_dvd_right hq_dvd_p_sub_one hcop
  have hq_dvd_b : q ∣ b := by
    have hq_dvd_ub : q ∣ u * b := by
      simpa [hN, mul_comm] using hq_dvd_N
    exact huq.symm.dvd_of_dvd_mul_left hq_dvd_ub
  rcases hq_dvd_b with ⟨k, hk⟩
  have hkpos : 0 < k := by
    have hbpos : 0 < b := hbOdd.pos
    by_contra hnot
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hk0, Nat.mul_zero] at hk
    omega
  have hprodOdd : Odd (q * k) := by
    rw [← hk]
    exact hbOdd
  have hkOdd : Odd k := Nat.Odd.of_mul_right hprodOdd
  have hk_le_two : k ≤ 2 := by
    by_contra hnot
    have hk3 : 3 ≤ k := by omega
    have hle : 3 * q ≤ q * k := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left q hk3
    have hqpos : 0 < q := hqPrime.pos
    omega
  have hk1 : k = 1 := by
    rcases hkOdd with ⟨t, ht⟩
    omega
  rw [hk1, mul_one] at hk
  exact hk

public theorem theorem_13_15
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
      case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u →
      (p % q ≠ 1 → u = (p ^ q - 1) / (p - 1)) ∧
        (p % q = 1 → u = (p ^ q - 1) / (q * (p - 1))) := by
  intro hsource hcaseB
  rcases section13_15_primes_odd_ne Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hsource hcaseB with
    ⟨hpPrime, hqPrime, hpOdd, hqOdd, _hp_ne_q, _hp3, _hq3⟩
  have hdiv : u ∣ (p ^ q - 1) / (p - 1) :=
    Section9.case_9_7_b_u_dvd_sec9 hcaseB
  rcases hdiv with ⟨b, hb0⟩
  have hN : (p ^ q - 1) / (p - 1) = b * u := by
    simpa [mul_comm] using hb0
  have hb_le : b ≤ 2 * q :=
    section13_15_factor_le_two_mul_q
      Smax Tmax W W1 W2 P Q U V C D Sfam Tfam τS τT
      p q u v c d b hsource hcaseB hN
  constructor
  · intro hmod_ne
    have hb_eq_one : b = 1 :=
      section13_15_factor_eq_one_of_mod_ne hpPrime hqPrime hpOdd hqOdd
        hmod_ne hN hb_le
    rw [hb_eq_one, one_mul] at hN
    exact hN.symm
  · intro hmod
    have hcop : Nat.Coprime u (p - 1) :=
      Section9.case_9_7_b_coprime_u_p_minus_one_sec9 hcaseB
    have hb_eq_q : b = q :=
      section13_15_factor_eq_q_of_mod_eq hpPrime hqPrime hpOdd hqOdd
        hmod hcop hN hb_le
    have hN_uq : (p ^ q - 1) / (p - 1) = q * u := by
      simpa [hb_eq_q, mul_comm] using hN
    have hu_div : u = ((p ^ q - 1) / (p - 1)) / q := by
      rw [hN_uq]
      exact (Nat.mul_div_right u hqPrime.pos).symm
    have hdivdiv :
        ((p ^ q - 1) / (p - 1)) / q =
          (p ^ q - 1) / (q * (p - 1)) := by
      rw [Nat.mul_comm q (p - 1), ← Nat.div_div_eq_div_mul]
    exact hu_div.trans hdivdiv
end CFSG.Section13
