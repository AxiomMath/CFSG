module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_14

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 14: theorem (14.15)
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section14

universe u v w

/-! ## (14.15) -/


public theorem section14_theorem_14_15_final_numeric_contradiction
    {p q u h x : ℕ}
    (hq : q = 3)
    (hp : p = 7)
    (hu : u = 19)
    (hh : h = u * x)
    (hx : 31 ≤ x)
    (hineq :
      ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) ≤
        ((p * q - 1 : ℕ) : ℝ)) :
    False := by
  subst q
  subst p
  subst u
  subst h
  have hxmul : 31 * 19 ≤ 19 * x := by nlinarith
  have hnum : 31 * 19 - 1 ≤ 19 * x - 1 :=
    Nat.sub_le_sub_right hxmul 1
  have hreal : (588 : ℝ) ≤ ((19 * x - 1 : ℕ) : ℝ) := by
    norm_num
    exact_mod_cast hnum
  norm_num at hineq
  have hupper : ((19 * x - 1 : ℕ) : ℝ) ≤ 420 := by
    have hpos : (0 : ℝ) < 21 := by norm_num
    have hmul := (div_le_iff₀ hpos).mp hineq
    norm_num at hmul ⊢
    exact hmul
  have hbad : (588 : ℝ) ≤ 420 := le_trans hreal hupper
  norm_num at hbad

public theorem section14_theorem_14_15_final_numeric_package_of_inputs
    {p q u h x : ℕ}
    (hq : q = 3)
    (hp : p = 7)
    (hqu : q * u = (p ^ q - 1) / (p - 1))
    (hh : h = u * x)
    (hx : q + (1 + q) * p ≤ x)
    (hineq :
      ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) ≤
        ((p * q - 1 : ℕ) : ℝ)) :
    q = 3 ∧ p = 7 ∧ u = 19 ∧ h = u * x ∧ 31 ≤ x ∧
      ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) ≤
        ((p * q - 1 : ℕ) : ℝ) := by
  subst q
  subst p
  norm_num at hqu hx ⊢
  have hu : u = 19 := by omega
  exact ⟨hu, hh, hx, hineq⟩

public theorem section14_theorem_14_15_product_formula_of_source_case
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hsrc : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcase :
      Section13.case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (hq : q = 3)
    (hp : p = 7)
    (hmod : p % q = 1) :
    q * u = (p ^ q - 1) / (p - 1) := by
  have hforms := Section13.theorem_13_15 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d hsrc hcase
  have hu : u = (p ^ q - 1) / (q * (p - 1)) := hforms.2 hmod
  subst q
  subst p
  norm_num at hu ⊢
  omega

public theorem section14_theorem_14_15_product_formula_of_mod_eq_one
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hsrc : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (hcase :
      Section13.case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (hqp : q < p)
    (h2q : 2 < q)
    (hmod : p % q = 1) :
    q * u = (p ^ q - 1) / (p - 1) := by
  have hcase' := hcase
  rcases hcase' with
    ⟨_h92, _hH0, _hquot, hpPrime, hqPrime, _ho, _hcard, _hcent, _hcyc,
      _hirr, _hfield, _hcop, _hdiv, _hprimeField⟩
  have hpOdd : Odd p := hpPrime.odd_of_ne_two (by omega)
  have hqOdd : Odd q := hqPrime.odd_of_ne_two (by omega)
  have hgeom_dvd : q ∣ (p ^ q - 1) / (p - 1) :=
    (Section13.theorem_13_14 p q 1 hpPrime hqPrime hpOdd hqOdd).2.1 hmod
  have hforms := Section13.theorem_13_15 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d hsrc hcase
  have hu : u = (p ^ q - 1) / (q * (p - 1)) := hforms.2 hmod
  have hdivdiv :
      (p ^ q - 1) / (q * (p - 1)) = ((p ^ q - 1) / (p - 1)) / q := by
    rw [Nat.mul_comm q (p - 1), ← Nat.div_div_eq_div_mul]
  rw [hu, hdivdiv]
  exact Nat.mul_div_cancel' hgeom_dvd

public theorem section14_theorem_14_15_case_a_ineq_of_alternative
    {G : Type u} [Group G] [Finite G]
    {βMτ βLτ φτ ψτ : Section1.ClassFunction G}
    {p q h : ℕ}
    (hp : p = 7)
    (h1414 : theorem_14_14_alternative βMτ βLτ φτ ψτ p q h) :
    ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) ≤
      ((p * q - 1 : ℕ) : ℝ) := by
  rcases h1414 with hcaseA | hcaseB
  · exact hcaseA.2
  · rcases hcaseB with ⟨_hsp, _hq, hp5⟩
    omega

public theorem section14_theorem_14_15_case_a_ineq_of_mod_eq_one
    {G : Type u} [Group G] [Finite G]
    {βMτ βLτ φτ ψτ : Section1.ClassFunction G}
    {p q h : ℕ}
    (hmod : p % q = 1)
    (h1414 : theorem_14_14_alternative βMτ βLτ φτ ψτ p q h) :
    ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) ≤
      ((p * q - 1 : ℕ) : ℝ) := by
  rcases h1414 with hcaseA | hcaseB
  · exact hcaseA.2
  · rcases hcaseB with ⟨_hsp, hq, hp⟩
    subst q
    subst p
    norm_num at hmod

public theorem section14_theorem_14_15_mod_eq_one_of_not_formula
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            Section13.case_9_7_b_for_section13 Smax C p q u →
              theorem_14_5_data L H W1 W2 Q →
                u ≠ (p ^ q - 1) / (p - 1) →
                  p % q = 1 := by
  intro hctx h143 h1410 h1413 hcaseB h145 hneq
  have hcaseSource :
      Section13.case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u :=
    section14_theorem_14_6_source_data_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143
  have hforms := Section13.theorem_13_15 Smax Tmax W W1 W2 P Q U V C D
    Sfam Tfam τS τT p q u v c d hctx.1 hcaseSource
  by_contra hmod
  exact hneq (hforms.1 hmod)

public theorem section14_theorem_14_15_p_eq_seven_of_q_eq_three_and_bound
    {p q : ℕ}
    (hp : Nat.Prime p)
    (hqp : q < p)
    (hmod : p % q = 1)
    (hq : q = 3)
    (hp_lt : p < q ^ 2) :
    p = 7 := by
  subst q
  norm_num at hmod hp_lt
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 4) hp)
  · norm_num at hmod
  · exact False.elim ((by decide : ¬ Nat.Prime 6) hp)
  · rfl
  · exact False.elim ((by decide : ¬ Nat.Prime 8) hp)

public theorem section14_theorem_14_15_q_eq_three_of_pow_bound
    {p q : ℕ}
    (hq : Nat.Prime q)
    (h2q : 2 < q)
    (hqp : q < p)
    (hpow : p ^ (q - 2) < q ^ 2) :
    q = 3 := by
  by_contra hq3
  have hq2_ne : q ≠ 2 := by omega
  have hq5 : 5 ≤ q := Nat.Prime.five_le_of_ne_two_of_ne_three hq hq2_ne hq3
  have hq2_lt_p2 : q ^ 2 < p ^ 2 := by
    exact Nat.pow_lt_pow_left hqp (by norm_num)
  have hp2_le : p ^ 2 ≤ p ^ (q - 2) := by
    exact Nat.pow_le_pow_right (by omega : 0 < p) (by omega : 2 ≤ q - 2)
  omega

public theorem section14_theorem_14_15_q_eq_three_and_p_lt_q_sq_of_pow_bound
    {p q : ℕ}
    (hq : Nat.Prime q)
    (h2q : 2 < q)
    (hqp : q < p)
    (hpow : p ^ (q - 2) < q ^ 2) :
    q = 3 ∧ p < q ^ 2 := by
  have hqeq : q = 3 :=
    section14_theorem_14_15_q_eq_three_of_pow_bound hq h2q hqp hpow
  constructor
  · exact hqeq
  · subst q
    norm_num at hpow ⊢
    exact hpow

public theorem section14_theorem_14_15_pow_bound_of_h_gt_and_ineq
    {p q h : ℕ}
    (hp : Nat.Prime p)
    (h2q : 2 < q)
    (hgt : p ^ q + 1 < h)
    (hineq :
      ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) ≤
        ((p * q - 1 : ℕ) : ℝ)) :
    p ^ (q - 2) < q ^ 2 := by
  have hp_pos : 0 < p := hp.pos
  have hq_pos : 0 < q := by omega
  have hpq_pos : 0 < p * q := Nat.mul_pos hp_pos hq_pos
  have hsub_gt : p ^ q < h - 1 := by omega
  have hdiv_lt : ((p ^ q : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) < (p * q : ℝ) := by
    have hleft :
        ((p ^ q : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) <
          ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) := by
      exact div_lt_div_of_pos_right
        (by exact_mod_cast hsub_gt) (by exact_mod_cast hpq_pos)
    have hright : ((p * q - 1 : ℕ) : ℝ) < (p * q : ℝ) := by
      have : p * q - 1 < p * q := by omega
      exact_mod_cast this
    exact lt_trans hleft (lt_of_le_of_lt hineq hright)
  have hpow_lt_sq : (p : ℝ) ^ q < ((p * q : ℕ) : ℝ) ^ 2 := by
    have hden_pos : (0 : ℝ) < ((p * q : ℕ) : ℝ) := by exact_mod_cast hpq_pos
    have htmp := hdiv_lt
    field_simp [ne_of_gt hden_pos] at htmp
    norm_num [pow_two] at htmp ⊢
    nlinarith
  have hpow_decomp : (p : ℝ) ^ q = (p : ℝ) ^ (q - 2) * (p : ℝ) ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hsq_expand : ((p * q : ℕ) : ℝ) ^ 2 = (p : ℝ) ^ 2 * (q : ℝ) ^ 2 := by
    norm_num [pow_two]
    ring
  have hp2_pos : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
  have hreal : (p : ℝ) ^ (q - 2) < (q : ℝ) ^ 2 := by
    rw [hpow_decomp, hsq_expand] at hpow_lt_sq
    nlinarith
  exact_mod_cast hreal

public theorem section14_theorem_14_15_mul_geom_gt_pow_succ
    {p q : ℕ}
    (hp : Nat.Prime p)
    (h2q : 2 < q) :
    p ^ q + 1 < p * ((p ^ q - 1) / (p - 1)) := by
  have hp2 : 2 ≤ p := hp.two_le
  rw [← Nat.geomSum_eq hp2 q]
  have hq_pos : 0 < q := by omega
  have hq_pred_lt : q - 1 < q := by omega
  have hmem_last : q - 1 ∈ Finset.range q := by simpa using hq_pred_lt
  have hmem_zero : 0 ∈ Finset.range q := by simpa using hq_pos
  have hne : 0 ≠ q - 1 := by omega
  have hsum_ge : p ^ 0 + p ^ (q - 1) ≤ ∑ x ∈ Finset.range q, p ^ x := by
    exact Finset.add_le_sum (s := Finset.range q) (f := fun x => p ^ x)
      (by intro x hx; exact Nat.zero_le _) hmem_zero hmem_last hne
  have hmul_ge :
      p * (p ^ 0 + p ^ (q - 1)) ≤ p * ∑ x ∈ Finset.range q, p ^ x :=
    Nat.mul_le_mul_left p hsum_ge
  have hpow : p * p ^ (q - 1) = p ^ q := by
    rw [Nat.mul_comm, ← pow_succ]
    congr 1
    omega
  have hstrict : p ^ q + 1 < p * (p ^ 0 + p ^ (q - 1)) := by
    rw [pow_zero, Nat.mul_add, Nat.mul_one, hpow]
    omega
  exact lt_of_lt_of_le hstrict hmul_ge

public theorem section14_theorem_14_15_h_gt_of_product_and_x_lower
    {p q u h x : ℕ}
    (hp : Nat.Prime p)
    (h2q : 2 < q)
    (hqu : q * u = (p ^ q - 1) / (p - 1))
    (hh : h = u * x)
    (hx : q + (1 + q) * p ≤ x) :
    p ^ q + 1 < h := by
  let geom := (p ^ q - 1) / (p - 1)
  have hgeom_gt : p ^ q + 1 < p * geom := by
    dsimp [geom]
    exact section14_theorem_14_15_mul_geom_gt_pow_succ hp h2q
  have hgeom_pos : 0 < geom := by
    by_contra hnot
    have hzero : geom = 0 := by omega
    rw [hzero, Nat.mul_zero] at hgeom_gt
    omega
  have hu_pos : 0 < u := by
    by_contra hnot
    have hu0 : u = 0 := by omega
    rw [hu0, Nat.mul_zero] at hqu
    omega
  have hx_gt : p * q < x := by
    nlinarith
  have hux_gt : u * (p * q) < u * x :=
    Nat.mul_lt_mul_of_pos_left hx_gt hu_pos
  have hpgeom_lt_h : p * geom < h := by
    rw [hh]
    calc
      p * geom = u * (p * q) := by
        dsimp [geom]
        rw [← hqu]
        ring
      _ < u * x := hux_gt
  exact lt_trans hgeom_gt hpgeom_lt_h

public theorem section14_theorem_14_15_x_lower_of_decomp_mod_and_odd
    {p q x n : ℕ}
    (hpOdd : Odd p)
    (hqOdd : Odd q)
    (hxn : x = q + n * p)
    (hnmod : n % q = 1)
    (hxOdd : Odd x) :
    q + (1 + q) * p ≤ x := by
  have hn_ne_one : n ≠ 1 := by
    intro hn1
    subst n
    have hx_eq : x = q + p := by
      simpa [Nat.mul_comm] using hxn
    have hxEven : Even x := by
      rw [hx_eq]
      exact Odd.add_odd hqOdd hpOdd
    exact Nat.not_even_iff_odd.mpr hxOdd hxEven
  have hn_eq : 1 + q * (n / q) = n := by
    simpa [hnmod] using (Nat.mod_add_div n q)
  have hdiv_ne_zero : n / q ≠ 0 := by
    intro hzero
    apply hn_ne_one
    rw [hzero, Nat.mul_zero, Nat.add_zero] at hn_eq
    exact hn_eq.symm
  have hdiv_pos : 1 ≤ n / q :=
    Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hdiv_ne_zero)
  have hn_ge : 1 + q ≤ n := by
    nlinarith [Nat.mul_le_mul_left q hdiv_pos]
  rw [hxn]
  have hmul : (1 + q) * p ≤ n * p :=
    Nat.mul_le_mul_right p hn_ge
  exact Nat.add_le_add_left hmul q

public theorem section14_theorem_14_15_x_lower_of_mods_and_odd
    {p q x : ℕ}
    (hpOdd : Odd p)
    (hqOdd : Odd q)
    (hpmod : p % q = 1)
    (hxp : x % p = q)
    (hxq : x % q = 1)
    (hxOdd : Odd x) :
    q + (1 + q) * p ≤ x := by
  let n := x / p
  have hxn : x = q + n * p := by
    have hx_eq : q + p * (x / p) = x := by
      simpa [hxp] using (Nat.mod_add_div x p)
    simpa [n, Nat.mul_comm] using hx_eq.symm
  have hnmod : n % q = 1 := by
    have hxq' : (q + n * p) % q = 1 := by
      rw [← hxn]
      exact hxq
    have hcalc : (q + n * p) % q = n % q := by
      rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mul_mod, hpmod]
      simp
    rw [hcalc] at hxq'
    exact hxq'
  exact section14_theorem_14_15_x_lower_of_decomp_mod_and_odd
    hpOdd hqOdd hxn hnmod hxOdd

public theorem section14_theorem_14_15_geom_quotient_mod_p_eq_one
    {p q : ℕ}
    (hp : Nat.Prime p)
    (hqpos : 0 < q) :
    ((p ^ q - 1) / (p - 1)) % p = 1 := by
  rw [← Nat.geomSum_eq hp.two_le q]
  induction q with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero =>
          simp [Nat.mod_eq_of_lt hp.one_lt]
      | succ n =>
          rw [Finset.sum_range_succ]
          have hprev : (∑ i ∈ Finset.range (n + 1), p ^ i) % p = 1 :=
            ih (by omega)
          have hpowmod : p ^ (n + 1) % p = 0 := by
            rw [Nat.mod_eq_zero_of_dvd]
            exact dvd_pow_self p (by omega : n + 1 ≠ 0)
          rw [Nat.add_mod, hprev, hpowmod]
          exact Nat.mod_eq_of_lt hp.one_lt

public theorem section14_theorem_14_15_mod_eq_one_of_dvd_sub_one
    {q n : ℕ}
    (hq : 1 < q)
    (hn : 0 < n)
    (hdiv : q ∣ n - 1) :
    n % q = 1 := by
  have h1n : 1 ≡ n [MOD q] :=
    (Nat.modEq_iff_dvd' (by omega : 1 ≤ n)).mpr hdiv
  have hn1 : n ≡ 1 [MOD q] := h1n.symm
  rw [Nat.ModEq] at hn1
  simpa [Nat.mod_eq_of_lt hq] using hn1

public theorem section14_theorem_14_15_u_mod_q_eq_one
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {p q u v c d : ℕ}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h2q : 2 < q) :
    u % q = 1 := by
  have hsrc : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d := hctx.1
  rcases hsrc with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, hqcard, _hC, _hD, _hccard, _hd,
      hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hBetaSupportNorm, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  rcases Section13.theorem_13_2 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hctx.1 with
    ⟨_hSmaxMF, _htypeS, _htypeII, _hUcomm, hUfrob, _hPelem,
      _hPcard, _hu, _hSfamCoh, _hTI, _hTauS⟩
  have hc_one : c = 1 :=
    Section13.theorem_13_12 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hctx.1
  have hUcard_eq : Nat.card U = u := by
    rw [hUcard, hc_one, Nat.mul_one]
  have hdivCard : Nat.card W1 ∣ Nat.card U - 1 :=
    section14_frobeniusJoin_complement_card_dvd_kernel_card_sub_one U W1 hUfrob
  have hdivU : Nat.card W1 ∣ u - 1 := by
    rw [hUcard_eq] at hdivCard
    exact hdivCard
  have hdiv : q ∣ u - 1 := by
    rw [hqcard]
    exact hdivU
  have hu_pos : 0 < u := by
    rw [← hUcard_eq]
    exact Nat.card_pos
  exact section14_theorem_14_15_mod_eq_one_of_dvd_sub_one
    (by omega : 1 < q) hu_pos hdiv

public theorem section14_theorem_14_15_x_mod_p_of_h_mod_p_and_product
    {p q u h x : ℕ}
    (hp : Nat.Prime p)
    (h2q : 2 < q)
    (hqp : q < p)
    (hqu : q * u = (p ^ q - 1) / (p - 1))
    (hh : h = u * x)
    (hhp : h % p = 1) :
    x % p = q := by
  have hgeom_mod : ((p ^ q - 1) / (p - 1)) % p = 1 :=
    section14_theorem_14_15_geom_quotient_mod_p_eq_one hp (by omega)
  have hhMod : h ≡ 1 [MOD p] := by
    rw [Nat.ModEq]
    simpa [Nat.mod_eq_of_lt hp.one_lt] using hhp
  have hleft : q * h ≡ q * 1 [MOD p] := (Nat.ModEq.refl q).mul hhMod
  have hright : ((p ^ q - 1) / (p - 1)) * x ≡ 1 * x [MOD p] := by
    have hg : ((p ^ q - 1) / (p - 1)) ≡ 1 [MOD p] := by
      rw [Nat.ModEq]
      simpa [Nat.mod_eq_of_lt hp.one_lt] using hgeom_mod
    exact hg.mul (Nat.ModEq.refl x)
  have hcalc : q * h = ((p ^ q - 1) / (p - 1)) * x := by
    rw [hh, ← hqu]
    ring
  have hxMod : x ≡ q [MOD p] := by
    have hqh : q * h ≡ q [MOD p] := by
      simpa using hleft
    have hgeomx : ((p ^ q - 1) / (p - 1)) * x ≡ x [MOD p] := by
      simpa using hright
    have hqh' : ((p ^ q - 1) / (p - 1)) * x ≡ q [MOD p] := by
      simpa [hcalc] using hqh
    exact hgeomx.symm.trans hqh'
  rw [Nat.ModEq] at hxMod
  have hqmod : q % p = q := Nat.mod_eq_of_lt hqp
  simpa [hqmod] using hxMod

public theorem section14_theorem_14_15_x_mod_q_of_h_mod_q_and_u_mod_q
    {q u h x : ℕ}
    (hq : 1 < q)
    (hh : h = u * x)
    (hhq : h % q = 1)
    (huq : u % q = 1) :
    x % q = 1 := by
  have hhMod : h ≡ 1 [MOD q] := by
    rw [Nat.ModEq]
    simpa [Nat.mod_eq_of_lt hq] using hhq
  have huMod : u ≡ 1 [MOD q] := by
    rw [Nat.ModEq]
    simpa [Nat.mod_eq_of_lt hq] using huq
  have hux : u * x ≡ 1 * x [MOD q] := huMod.mul (Nat.ModEq.refl x)
  have hxMod : x ≡ 1 [MOD q] := by
    have hux' : u * x ≡ 1 [MOD q] := by
      simpa [hh] using hhMod
    simpa using hux.symm.trans hux'
  rw [Nat.ModEq] at hxMod
  simpa [Nat.mod_eq_of_lt hq] using hxMod

public theorem section14_exists_h_eq_u_mul_of_hypotheses
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
        Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_13_statement L M H h →
          ∃ x : ℕ, h = u * x := by
  intro hctx h143 h1413
  rcases section14_theorem_14_5_pf13_17_inputs hctx h143 with
    ⟨_htypeII, _hfrobLH, hUH, _hcomp⟩
  have hsrc : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d := hctx.1
  rcases hsrc with
    ⟨_hcase, _hSTypeP, _hTTypeP, _hp, _hq, _hC, _hD, _hc, _hd, hUcard,
      _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hBetaSupportNorm, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  have hc_one : c = 1 :=
    Section13.theorem_13_12 Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d hctx.1
  have hUcard_eq : Nat.card U = u := by
    rw [hUcard, hc_one, Nat.mul_one]
  rcases Subgroup.card_dvd_of_le hUH with ⟨x, hx⟩
  exact ⟨x, by rw [h1413.2, hx, hUcard_eq]⟩


public theorem section14_odd_h_of_odd_L
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax L H M P Q U W1 W2 : Subgroup G}
    {Lfam : Finset (Section1.ClassFunction L)}
    {RL : G → Subgroup G}
    {τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ : Section1.ClassFunction L}
    {μ01 : Section1.ClassFunction Smax}
    {ν10 : Section1.ClassFunction Tmax}
    {βS : Section1.ClassFunction Smax}
    {βT : Section1.ClassFunction Tmax}
    {βL : Section1.ClassFunction L}
    {h : ℕ}
    (h143 : hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL)
    (h1413 : hypothesis_14_13_statement L M H h)
    (hLOdd : Odd (Nat.card L)) :
    Odd h := by
  rcases h143 with
    ⟨_hLmax, _hNormUleL, hLHMf, _hTypeI, _hDadeL, _hLfam, _h52b, _hExt,
      _hφmem, _hφirr, _hφdeg, _hβS, _hβT, _hβL, _hDadeNotation⟩
  have hHL : H ≤ L := Section12.section16MFSubgroup_le hLHMf
  have hHOdd : Odd (Nat.card H) :=
    Odd.of_dvd_nat hLOdd (Subgroup.card_dvd_of_le hHL)
  rw [h1413.2]
  exact hHOdd


public theorem section14_odd_L_of_typeI
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    (hTypeI : Section8.typeIDefinitionData L H) :
    Odd (Nat.card L) :=
  Section12.odd_card_of_typeIDefinitionData L H hTypeI


public theorem section14_theorem_13_19_eta_outputs_of_hypothesis_14_3
    {G : Type u} [Group G] [Finite G]
    {Smax Tmax W W1 W2 P Q U V C D L H : Subgroup G}
    {Sfam : Finset (Section1.ClassFunction Smax)}
    {Tfam : Finset (Section1.ClassFunction Tmax)}
    {τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G}
    {τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G}
    {Lfam : Finset (Section1.ClassFunction L)}
    {RL : G → Subgroup G}
    {τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {φ : Section1.ClassFunction L}
    {μ01 : Section1.ClassFunction Smax}
    {ν10 : Section1.ClassFunction Tmax}
    {βS : Section1.ClassFunction Smax}
    {βT : Section1.ClassFunction Tmax}
    {βL : Section1.ClassFunction L}
    {p q u v c d : ℕ}
    {η : Fin q → Fin p → Section1.ClassFunction G}
    (hctx : hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d)
    (h143 : hypothesis_14_3_data Smax Tmax L H P Q U W1 W2
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL)
    (heta : section14EtaData Smax Tmax W W1 W2 p q η) :
    ∃ ηNat : ℕ → ℕ → Section1.ClassFunction G,
    ∃ μNat : ℕ → ℕ → Section1.ClassFunction Smax,
    ∃ νNat : ℕ → ℕ → Section1.ClassFunction Tmax,
      (∀ i j, η i j = ηNat (i : ℕ) (j : ℕ)) ∧
        (∀ i j, Section1.scalarProduct G (τL₁ φ) (η i j) = 0) ∧
        Section13.theorem_13_19_alternativeData H (τL βL)
          (τS (Section7.principalInducedCharacter Smax (P ⊔ W1) - μNat 0 1))
          (τL₁ φ) ηNat p q u (H.relIndex L) ∧
        Section13.theorem_13_19_alternativeData H (τL βL)
          (τT (Section7.principalInducedCharacter Tmax (Q ⊔ W2) - νNat 1 0))
          (τL₁ φ) (fun i j => ηNat j i) q p v (H.relIndex L) := by
  rcases h143 with
    ⟨hLmax, _hNorm, hMF, hTypeI, hDade, hLfam, _h52b, hExt,
      hφmem, _hφirr, hφdeg, _hβS, _hβT, hβL, _hDadeNotation⟩
  rcases heta with
    ⟨ω, ηNat, μ, ν, μsum, νsum, δ, δ', σ, hnotation, hη⟩
  have hhyp :
      Section13.theorem_13_19_hypothesis L H Smax P W1 Lfam RL τS τL τL₁
        φ (τL₁ φ) (μ 0 1) (τL βL)
        (τS (Section7.principalInducedCharacter Smax (P ⊔ W1) - μ 0 1))
        (H.relIndex L) := by
    refine ⟨hLmax, hMF, hTypeI, rfl, hDade, hLfam, hExt, hφmem,
      hφdeg, rfl, ?_, ?_⟩
    · simpa [Section7.theorem_7_8_betaInput,
        Section7.principalInducedCharacter] using congrArg τL hβL
    · simp [Section7.principalInducedCharacter]
  have h1319 := Section13.theorem_13_19
    Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam Lfam RL
    τS τT τL τL₁ φ (τL βL)
    (τS (Section7.principalInducedCharacter Smax (P ⊔ W1) - μ 0 1)) (τL₁ φ)
    ω ηNat μ ν μsum νsum δ δ' σ p q u v c d (H.relIndex L)
    hctx.1 hnotation hhyp
  have hhypT :
      Section13.theorem_13_19_hypothesis L H Tmax Q W2 Lfam RL τT τL τL₁
        φ (τL₁ φ) (ν 1 0) (τL βL)
        (τT (Section7.principalInducedCharacter Tmax (Q ⊔ W2) - ν 1 0))
        (H.relIndex L) := by
    refine ⟨hLmax, hMF, hTypeI, rfl, hDade, hLfam, hExt, hφmem,
      hφdeg, rfl, ?_, ?_⟩
    · simpa [Section7.theorem_7_8_betaInput,
        Section7.principalInducedCharacter] using congrArg τL hβL
    · simp [Section7.principalInducedCharacter]
  have h1319T := Section13.theorem_13_19
    Tmax Smax W W2 W1 Q P V U D C L H Tfam Sfam Lfam RL
    τT τS τL τL₁ φ (τL βL)
    (τT (Section7.principalInducedCharacter Tmax (Q ⊔ W2) - ν 1 0)) (τL₁ φ)
    (fun i j => ω j i) (fun i j => ηNat j i)
    (fun i j => ν j i) (fun i j => μ j i)
    (fun i => νsum i) (fun i => μsum i) δ' δ σ q p v u d c
    (H.relIndex L)
    (section14_hypothesis_13_1_sourceData_swap hctx.1)
    (section14_hypothesis_13_1_characterNotationDataFor_swap hnotation)
    hhypT
  refine ⟨ηNat, μ, ν, hη, ?_, h1319.2.2.2, h1319T.2.2.2⟩
  intro i j
  rw [hη i j]
  exact h1319.2.1 φ hφmem (i : ℕ) (j : ℕ) i.isLt j.isLt

public theorem section14_fixedPointFree_h_divisibility_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
        hypothesis_14_13_statement L M H h →
          theorem_14_5_data L H W1 W2 Q →
            2 < q ∧ p ∣ h - 1 ∧ q ∣ h - 1 ∧
              ∀ x : ℕ, h = u * x → Odd x := by
  intro hctx h143 h1410 h1413 h145
  -- Textbook fixed-point-free source package used in PF `(14.15)` and
  -- `(14.16)`: PF `(14.5)` gives a complement containing the `p`- and
  -- `q`-parts, so fixed-point-freeness gives divisibility of `h - 1`; the
  -- parity of `h` is the remaining source action fact.
  rcases section14_theorem_14_5_pf13_17_inputs hctx h143 with
    ⟨_htypeII, hfrobLH, _hUH, _hcomp⟩
  rcases h145 with ⟨y, _hyQ, hsemi⟩
  have hsrc : Section13.hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
      Sfam Tfam τS τT p q u v c d := hctx.1
  rcases hsrc with
    ⟨_hcase, _hSTypeP, _hTTypeP, hp_card, hq_card, _hC, _hD, _hc, _hd,
      _hUcard, _hVcard, _hSfam, _hTfam, _hDadeS, _hDadeT, _hNotation, _hDadeDiff, _hZeroDegree, _hConjIndex, _hConjBetaTau, _hBetaSupportNorm, _hChoice, _hMin, _hFourSixS, _hFourSixT⟩
  let E : Subgroup G := W1 ⊔ W2.conjBy y
  have hEdiv : Nat.card E ∣ Nat.card H - 1 := by
    simpa [E] using
      section14_frobeniusWithKernel_complement_card_dvd_kernel_card_sub_one hfrobLH hsemi
  have hp_dvd : p ∣ h - 1 := by
    have hW2conj_card : Nat.card (W2.conjBy y) = Nat.card W2 :=
      section11_card_conjBy (G := G) W2 y
    have hW2div : Nat.card (W2.conjBy y) ∣ Nat.card E :=
      Subgroup.card_dvd_of_le (show W2.conjBy y ≤ E from by
        simp [E])
    have hW2div' : Nat.card W2 ∣ Nat.card E := by
      rw [← hW2conj_card]
      exact hW2div
    have hpdivE : p ∣ Nat.card E := by
      simpa [hp_card] using hW2div'
    exact by
      simpa [h1413.2] using hpdivE.trans hEdiv
  have hq_dvd : q ∣ h - 1 := by
    have hW1div : Nat.card W1 ∣ Nat.card E :=
      Subgroup.card_dvd_of_le (show W1 ≤ E from by
        simp [E])
    have hqdivE : q ∣ Nat.card E := by
      simpa [hq_card] using hW1div
    exact by
      simpa [h1413.2] using hqdivE.trans hEdiv
  have h2q : 2 < q := section14_two_lt_q_of_sourceData hctx
  have hTypeI : Section8.typeIDefinitionData L H := by
    rcases h143 with
      ⟨_hLmax, _hNorm, _hMF, hTypeI, _hDade, _hLfam, _h52b, _hExt,
        _hφmem, _hφirr, _hφdeg, _hβS, _hβT, _hβL, _hDadeNotation⟩
    exact hTypeI
  have hhOdd : Odd h :=
    section14_odd_h_of_odd_L h143 h1413 (section14_odd_L_of_typeI hTypeI)
  have hxOddAll : ∀ x : ℕ, h = u * x → Odd x := by
    intro x hx
    exact section14_odd_right_factor_of_mul_eq hhOdd hx
  exact ⟨h2q, hp_dvd, hq_dvd, hxOddAll⟩

public theorem section14_fixedPointFree_h_congruence_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
        hypothesis_14_13_statement L M H h →
          theorem_14_5_data L H W1 W2 Q →
            2 < q ∧ h % p = 1 ∧ h % q = 1 ∧
              ∀ x : ℕ, h = u * x → Odd x := by
  intro hctx h143 h1410 h1413 h145
  rcases section14_fixedPointFree_h_divisibility_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143 h1410 h1413 h145 with
    ⟨h2q, hp_dvd, hq_dvd, hxOddAll⟩
  rcases section14_context_primes_of_sourceData hctx with ⟨hpPrime, hqPrime⟩
  have hh_pos : 0 < h := by
    rw [h1413.2]
    exact Nat.card_pos
  have hhp : h % p = 1 :=
    section14_theorem_14_15_mod_eq_one_of_dvd_sub_one
      hpPrime.one_lt hh_pos hp_dvd
  have hhq : h % q = 1 :=
    section14_theorem_14_15_mod_eq_one_of_dvd_sub_one
      hqPrime.one_lt hh_pos hq_dvd
  exact ⟨h2q, hhp, hhq, hxOddAll⟩

public theorem section14_theorem_14_15_x_congruence_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
        hypothesis_14_13_statement L M H h →
          Section13.case_9_7_b_for_section13 Smax C p q u →
            theorem_14_5_data L H W1 W2 Q →
              u ≠ (p ^ q - 1) / (p - 1) →
                2 < q ∧ h % p = 1 ∧ h % q = 1 ∧
                  ∀ x : ℕ, h = u * x → Odd x := by
  intro hctx h143 h1410 h1413 _hcaseB h145 _hneq
  exact section14_fixedPointFree_h_congruence_source_bridge
    Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
    Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
    p q u v c d h hctx h143 h1410 h1413 h145

public theorem section14_theorem_14_15_x_inputs_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            Section13.case_9_7_b_for_section13 Smax C p q u →
              theorem_14_5_data L H W1 W2 Q →
                u ≠ (p ^ q - 1) / (p - 1) →
                  ∃ x : ℕ,
                    2 < q ∧ h = u * x ∧ q + (1 + q) * p ≤ x := by
  intro hctx h143 h1410 h1413 hcaseB h145 hneq
  rcases section14_exists_h_eq_u_mul_of_hypotheses
      Smax Tmax W W1 W2 P Q U V C D L H M Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d h
      hctx h143 h1413 with
    ⟨x, hh⟩
  rcases section14_theorem_14_15_x_congruence_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143 h1410 h1413 hcaseB h145 hneq with
    ⟨h2q, hhp, hhq, hxOddAll⟩
  have hxOdd : Odd x := hxOddAll x hh
  have hcaseB' := hcaseB
  have hcaseSource :
      Section13.case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u :=
    section14_theorem_14_6_source_data_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143
  rcases hcaseB with ⟨_hCM, hpPrime, hqPrime, _hcop, _hdiv⟩
  have hp_gt_two : 2 < p := lt_trans h2q hctx.2
  have hpOdd : Odd p :=
    hpPrime.odd_of_ne_two (ne_of_gt hp_gt_two)
  have hqOdd : Odd q :=
    hqPrime.odd_of_ne_two (ne_of_gt h2q)
  have hpmod : p % q = 1 :=
    section14_theorem_14_15_mod_eq_one_of_not_formula
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143 h1410 h1413 hcaseB' h145 hneq
  have hqu : q * u = (p ^ q - 1) / (p - 1) :=
    section14_theorem_14_15_product_formula_of_mod_eq_one
      hctx.1 hcaseSource hctx.2 h2q hpmod
  have hxp : x % p = q :=
    section14_theorem_14_15_x_mod_p_of_h_mod_p_and_product
      hpPrime h2q hctx.2 hqu hh hhp
  have huq : u % q = 1 :=
    section14_theorem_14_15_u_mod_q_eq_one hctx h2q
  have hxq : x % q = 1 :=
    section14_theorem_14_15_x_mod_q_of_h_mod_q_and_u_mod_q
      (by omega : 1 < q) hh hhq huq
  exact ⟨x, h2q, hh,
    section14_theorem_14_15_x_lower_of_mods_and_odd
      hpOdd hqOdd hpmod hxp hxq hxOdd⟩

public theorem section14_theorem_14_15_x_growth_inputs_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            Section13.case_9_7_b_for_section13 Smax C p q u →
              theorem_14_5_data L H W1 W2 Q →
                u ≠ (p ^ q - 1) / (p - 1) →
                  ∃ x : ℕ,
                    2 < q ∧ p ^ q + 1 < h ∧
                      h = u * x ∧ q + (1 + q) * p ≤ x := by
  intro hctx h143 h1410 h1413 hcaseB h145 hneq
  rcases section14_theorem_14_15_x_inputs_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143 h1410 h1413 hcaseB h145 hneq with
    ⟨x, h2q, hh, hx⟩
  have hcaseSource :
      Section13.case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u :=
    section14_theorem_14_6_source_data_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143
  have hmod : p % q = 1 :=
    section14_theorem_14_15_mod_eq_one_of_not_formula
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143 h1410 h1413 hcaseB h145 hneq
  have hqu : q * u = (p ^ q - 1) / (p - 1) :=
    section14_theorem_14_15_product_formula_of_mod_eq_one
      hctx.1 hcaseSource hctx.2 h2q hmod
  rcases hcaseB with ⟨_hCM, hpPrime, _hqPrime, _hcop, _hdiv⟩
  exact ⟨x, h2q,
    section14_theorem_14_15_h_gt_of_product_and_x_lower hpPrime h2q hqu hh hx,
    hh, hx⟩

public theorem section14_theorem_14_15_growth_inputs_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            Section13.case_9_7_b_for_section13 Smax C p q u →
              theorem_14_5_data L H W1 W2 Q →
                u ≠ (p ^ q - 1) / (p - 1) →
                  ∃ x : ℕ,
                    2 < q ∧ p ^ q + 1 < h ∧
                      h = u * x ∧ q + (1 + q) * p ≤ x ∧
                      ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) ≤
                        ((p * q - 1 : ℕ) : ℝ) := by
  intro hctx h143 h1410 h1413 hcaseB h145 hneq
  rcases section14_theorem_14_15_x_growth_inputs_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143 h1410 h1413 hcaseB h145 hneq with
    ⟨x, h2q, hgt, hh, hx⟩
  have hmod : p % q = 1 :=
    section14_theorem_14_15_mod_eq_one_of_not_formula
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143 h1410 h1413 hcaseB h145 hneq
  have h1414 :
      theorem_14_14_alternative (τM βM) (τL βL) (τL₁ φ) (τM₁ ψ) p q h :=
    section14_theorem_14_14_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      (τM βM) (τL βL) (τL₁ φ) (τM₁ ψ) p q u v c d h
      hctx h143 h1410 h1413 rfl rfl rfl rfl
  exact ⟨x, h2q, hgt, hh, hx,
    section14_theorem_14_15_case_a_ineq_of_mod_eq_one hmod h1414⟩

public theorem section14_theorem_14_15_pow_bound_inputs_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            Section13.case_9_7_b_for_section13 Smax C p q u →
              theorem_14_5_data L H W1 W2 Q →
                u ≠ (p ^ q - 1) / (p - 1) →
                  ∃ x : ℕ,
                    2 < q ∧ p ^ (q - 2) < q ^ 2 ∧
                      h = u * x ∧ q + (1 + q) * p ≤ x := by
  intro hctx h143 h1410 h1413 hcaseB h145 hneq
  rcases section14_theorem_14_15_growth_inputs_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143 h1410 h1413 hcaseB h145 hneq with
    ⟨x, h2q, hgt, hh, hx, hineq⟩
  rcases hcaseB with ⟨_hCM, hpPrime, _hqPrime, _hcop, _hdiv⟩
  exact ⟨x, h2q,
    section14_theorem_14_15_pow_bound_of_h_gt_and_ineq hpPrime h2q hgt hineq,
    hh, hx⟩

public theorem section14_theorem_14_15_q_three_bound_inputs_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            Section13.case_9_7_b_for_section13 Smax C p q u →
              theorem_14_5_data L H W1 W2 Q →
                u ≠ (p ^ q - 1) / (p - 1) →
                  ∃ x : ℕ,
                    q = 3 ∧ p < q ^ 2 ∧
                      h = u * x ∧ q + (1 + q) * p ≤ x := by
  intro hctx h143 h1410 h1413 hcaseB h145 hneq
  rcases section14_theorem_14_15_pow_bound_inputs_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143 h1410 h1413 hcaseB h145 hneq with
    ⟨x, h2q, hpow, hh, hx⟩
  rcases hcaseB with ⟨_hCM, _hpPrime, hqPrime, _hcop, _hdiv⟩
  rcases section14_theorem_14_15_q_eq_three_and_p_lt_q_sq_of_pow_bound
      hqPrime h2q hctx.2 hpow with
    ⟨hq, hp_lt⟩
  exact ⟨x, hq, hp_lt, hh, hx⟩

public theorem section14_theorem_14_15_numeric_congruence_inputs_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            Section13.case_9_7_b_for_section13 Smax C p q u →
              theorem_14_5_data L H W1 W2 Q →
                u ≠ (p ^ q - 1) / (p - 1) →
                  ∃ x : ℕ,
                    q = 3 ∧ p = 7 ∧
                      h = u * x ∧ q + (1 + q) * p ≤ x := by
  intro hctx h143 h1410 h1413 hcaseB h145 hneq
  rcases section14_theorem_14_15_q_three_bound_inputs_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143 h1410 h1413 hcaseB h145 hneq with
    ⟨x, hq, hp_lt, hh, hx⟩
  have hmod : p % q = 1 :=
    section14_theorem_14_15_mod_eq_one_of_not_formula
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143 h1410 h1413 hcaseB h145 hneq
  rcases hcaseB with ⟨_hCM, hpPrime, _hqPrime, _hcop, _hdiv⟩
  have hp : p = 7 :=
    section14_theorem_14_15_p_eq_seven_of_q_eq_three_and_bound
      hpPrime hctx.2 hmod hq hp_lt
  exact ⟨x, hq, hp, hh, hx⟩

public theorem section14_theorem_14_15_congruence_inputs_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            Section13.case_9_7_b_for_section13 Smax C p q u →
              theorem_14_5_data L H W1 W2 Q →
                u ≠ (p ^ q - 1) / (p - 1) →
                  ∃ x : ℕ,
                    p % q = 1 ∧ q = 3 ∧ p = 7 ∧
                      h = u * x ∧ q + (1 + q) * p ≤ x := by
  intro hctx h143 h1410 h1413 hcaseB h145 hneq
  have hmod : p % q = 1 :=
    section14_theorem_14_15_mod_eq_one_of_not_formula
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143 h1410 h1413 hcaseB h145 hneq
  rcases section14_theorem_14_15_numeric_congruence_inputs_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143 h1410 h1413 hcaseB h145 hneq with
    ⟨x, hq, hp, hh, hx⟩
  exact ⟨x, hmod, hq, hp, hh, hx⟩

public theorem section14_theorem_14_15_source_data_congruence_inputs_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            Section13.case_9_7_b_for_section13 Smax C p q u →
              theorem_14_5_data L H W1 W2 Q →
                u ≠ (p ^ q - 1) / (p - 1) →
                  ∃ x : ℕ,
                    Section13.case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u ∧
                      p % q = 1 ∧ q = 3 ∧ p = 7 ∧
                      h = u * x ∧ q + (1 + q) * p ≤ x := by
  intro hctx h143 h1410 h1413 hcaseB h145 hneq
  have hcaseSource :
      Section13.case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u :=
    section14_theorem_14_6_source_data_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143
  rcases section14_theorem_14_15_congruence_inputs_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143 h1410 h1413 hcaseB h145 hneq with
    ⟨x, hmod, hq, hp, hh, hx⟩
  exact ⟨x, hcaseSource, hmod, hq, hp, hh, hx⟩

public theorem section14_theorem_14_15_source_data_numeric_inputs_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            Section13.case_9_7_b_for_section13 Smax C p q u →
              theorem_14_5_data L H W1 W2 Q →
                u ≠ (p ^ q - 1) / (p - 1) →
                  ∃ x : ℕ,
                    Section13.case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u ∧
                      p % q = 1 ∧ q = 3 ∧ p = 7 ∧
                      h = u * x ∧ q + (1 + q) * p ≤ x ∧
                      ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) ≤
                        ((p * q - 1 : ℕ) : ℝ) := by
  intro hctx h143 h1410 h1413 hcaseB h145 hneq
  rcases section14_theorem_14_15_source_data_congruence_inputs_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143 h1410 h1413 hcaseB h145 hneq with
    ⟨x, hcaseSource, hmod, hq, hp, hh, hx⟩
  have h1414 :
      theorem_14_14_alternative (τM βM) (τL βL) (τL₁ φ) (τM₁ ψ) p q h :=
    section14_theorem_14_14_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      (τM βM) (τL βL) (τL₁ φ) (τM₁ ψ) p q u v c d h
      hctx h143 h1410 h1413 rfl rfl rfl rfl
  have hineq :
      ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) ≤
        ((p * q - 1 : ℕ) : ℝ) :=
    section14_theorem_14_15_case_a_ineq_of_alternative hp h1414
  exact ⟨x, hcaseSource, hmod, hq, hp, hh, hx, hineq⟩

public theorem section14_theorem_14_15_final_numeric_inputs_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            Section13.case_9_7_b_for_section13 Smax C p q u →
              theorem_14_5_data L H W1 W2 Q →
                u ≠ (p ^ q - 1) / (p - 1) →
                  ∃ x : ℕ,
                    q = 3 ∧ p = 7 ∧
                      q * u = (p ^ q - 1) / (p - 1) ∧
                      h = u * x ∧ q + (1 + q) * p ≤ x ∧
                      ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) ≤
                        ((p * q - 1 : ℕ) : ℝ) := by
  intro hctx h143 h1410 h1413 hcaseB h145 hneq
  rcases section14_theorem_14_15_source_data_numeric_inputs_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143 h1410 h1413 hcaseB h145 hneq with
    ⟨x, hcaseSource, hmod, hq, hp, hh, hx, hineq⟩
  have hqu : q * u = (p ^ q - 1) / (p - 1) :=
    section14_theorem_14_15_product_formula_of_source_case
      hctx.1 hcaseSource hq hp hmod
  exact ⟨x, hq, hp, hqu, hh, hx, hineq⟩

public theorem section14_theorem_14_15_final_numeric_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            Section13.case_9_7_b_for_section13 Smax C p q u →
              theorem_14_5_data L H W1 W2 Q →
                u ≠ (p ^ q - 1) / (p - 1) →
                  ∃ x : ℕ,
                    q = 3 ∧ p = 7 ∧ u = 19 ∧ h = u * x ∧ 31 ≤ x ∧
                      ((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) ≤
                        ((p * q - 1 : ℕ) : ℝ) := by
  intro hctx h143 h1410 h1413 hcaseB h145 hneq
  rcases section14_theorem_14_15_final_numeric_inputs_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143 h1410 h1413 hcaseB h145 hneq with
    ⟨x, hq, hp, hqu, hh, hx, hineq⟩
  exact ⟨x, section14_theorem_14_15_final_numeric_package_of_inputs
    hq hp hqu hh hx hineq⟩

public theorem section14_theorem_14_15_contradiction_with_case_b_and_complement_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            Section13.case_9_7_b_for_section13 Smax C p q u →
              theorem_14_5_data L H W1 W2 Q →
            u ≠ (p ^ q - 1) / (p - 1) →
              False := by
  intro hctx h143 h1410 h1413 hcaseB h145 hneq
  rcases section14_theorem_14_15_final_numeric_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
      p q u v c d h hctx h143 h1410 h1413 hcaseB h145 hneq with
    ⟨x, hq, hp, hu, hh, hx, hineq⟩
  exact section14_theorem_14_15_final_numeric_contradiction
    hq hp hu hh hx hineq

public theorem section14_theorem_14_15_contradiction_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            u ≠ (p ^ q - 1) / (p - 1) →
              False := by
  intro hctx h143 h1410 h1413 hneq
  have hcaseB : Section13.case_9_7_b_for_section13 Smax C p q u :=
    section14_theorem_14_6_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143
  have h145 : theorem_14_5_data L H W1 W2 Q :=
    section14_theorem_14_5_source_bridge
      Smax Tmax W W1 W2 P Q U V C D L H Sfam Tfam τS τT
      Lfam RL τL τL₁ φ μ01 ν10 βS βT βL p q u v c d hctx h143
  exact section14_theorem_14_15_contradiction_with_case_b_and_complement_source_bridge
    Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
    Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
    p q u v c d h hctx h143 h1410 h1413 hcaseB h145 hneq

public theorem section14_theorem_14_15_source_bridge
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (Smax Tmax W W1 W2 P Q U V C D L H M K : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (Lfam : Finset (Section1.ClassFunction L))
    (RL : G → Subgroup G)
    (τL τL₁ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (φ : Section1.ClassFunction L)
    (μ01 : Section1.ClassFunction Smax)
    (ν10 : Section1.ClassFunction Tmax)
    (βS : Section1.ClassFunction Smax)
    (βT : Section1.ClassFunction Tmax)
    (βL : Section1.ClassFunction L)
    (Mfam : Finset (Section1.ClassFunction M))
    (τM τM₁ : Section1.ClassFunction M →ₗ[ℂ] Section1.ClassFunction G)
    (ψ βM : Section1.ClassFunction M)
    (p q u v c d h : ℕ) :
    hypothesis_14_context_data Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      hypothesis_14_3_data Smax Tmax L H P Q U W1 W2 Lfam RL τL τL₁ φ μ01 ν10 βS βT βL →
        hypothesis_14_10_data M K V Mfam τM τM₁ ψ βM →
          hypothesis_14_13_statement L M H h →
            u = (p ^ q - 1) / (p - 1) := by
  intro hctx h143 h1410 h1413
  by_contra hneq
  exact section14_theorem_14_15_contradiction_source_bridge
    Smax Tmax W W1 W2 P Q U V C D L H M K Sfam Tfam τS τT
    Lfam RL τL τL₁ φ μ01 ν10 βS βT βL Mfam τM τM₁ ψ βM
    p q u v c d h hctx h143 h1410 h1413 hneq


end CFSG.Section14
