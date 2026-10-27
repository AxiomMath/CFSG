module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 14: theorem (14.8)
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section14

universe u v w

/-! ## (14.8) -/


public theorem section14_log_five_gt_six_fifths :
    Real.log (5 : ℝ) > (6 : ℝ) / 5 := by
  change (6 : ℝ) / 5 < Real.log 5
  rw [← Real.exp_lt_exp]
  have hexp_one : Real.exp (1 : ℝ) < 3 := by
    have h := Real.exp_bound' (x := (1 : ℝ)) (n := 4)
      (by norm_num) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ, pow_succ, Nat.factorial] at h ⊢
    linarith
  have hexp_fifth : Real.exp ((1 : ℝ) / 5) < 4 / 3 := by
    have h := Real.exp_bound' (x := ((1 : ℝ) / 5)) (n := 2)
      (by norm_num) (by norm_num) (by norm_num)
    norm_num [Finset.sum_range_succ, pow_succ, Nat.factorial] at h ⊢
    linarith
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 5)]
  have hsplit : Real.exp ((6 : ℝ) / 5) = Real.exp (1 + (1 / 5 : ℝ)) := by
    norm_num
  rw [hsplit, Real.exp_add]
  have hprod : Real.exp (1 : ℝ) * Real.exp ((1 : ℝ) / 5) < 3 * (4 / 3 : ℝ) :=
    mul_lt_mul hexp_one hexp_fifth.le (by positivity) (by positivity)
  nlinarith

public theorem section14_deriv_log_div_add_one (x : ℝ)
    (hx : x ≠ 0) (hx1 : x + 1 ≠ 0) :
    deriv (fun x : ℝ => Real.log x / (x + 1)) x =
      ((x + 1) / x - Real.log x) / (x + 1) ^ 2 := by
  change deriv ((fun x : ℝ => Real.log x) / (fun x : ℝ => x + 1)) x = _
  rw [deriv_div (Real.differentiableAt_log hx) (by fun_prop) hx1]
  rw [Real.deriv_log, show deriv (fun x : ℝ => x + 1) x = 1 by simp]
  field_simp [hx, hx1]

public theorem section14_strictAntiOn_log_div_add_one :
    StrictAntiOn (fun x : ℝ => Real.log x / (x + 1)) (Set.Ici 5) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici 5) ?hcont ?hderiv
  · apply ContinuousOn.div
    · exact ContinuousOn.log continuousOn_id (fun x hx => by
        have hx5 : (5 : ℝ) ≤ x := hx
        linarith)
    · exact continuousOn_id.add continuousOn_const
    · intro x hx
      have hx5 : (5 : ℝ) ≤ x := hx
      linarith
  · intro x hx
    have hx5 : 5 < x := by simpa [interior_Ici] using hx
    have hxpos : 0 < x := by linarith
    have hxne : x ≠ 0 := ne_of_gt hxpos
    have hx1ne : x + 1 ≠ 0 := by linarith
    rw [section14_deriv_log_div_add_one x hxne hx1ne]
    apply div_neg_of_neg_of_pos
    · have hle : (x + 1) / x ≤ (6 : ℝ) / 5 := by
        field_simp [hxne]
        nlinarith
      have hlog : (6 : ℝ) / 5 < Real.log x :=
        lt_trans section14_log_five_gt_six_fifths (Real.log_lt_log (by norm_num) hx5)
      linarith
    · positivity

public theorem section14_log_div_add_one_five_lt_three :
    Real.log (5 : ℝ) / ((5 : ℝ) + 1) <
      Real.log (3 : ℝ) / ((3 : ℝ) + 1) := by
  have hpow : (5 : ℝ) ^ 4 < (3 : ℝ) ^ 6 := by norm_num
  have hlog : Real.log ((5 : ℝ) ^ 4) < Real.log ((3 : ℝ) ^ 6) :=
    Real.log_lt_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  norm_num at hlog ⊢
  nlinarith

public theorem section14_log_div_add_one_prime_lt {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (h2q : 2 < q) (hqp : q < p) :
    Real.log (p : ℝ) / ((p : ℝ) + 1) <
      Real.log (q : ℝ) / ((q : ℝ) + 1) := by
  by_cases hq3 : q = 3
  · subst q
    have hp5le : 5 ≤ p := by
      have hp2 : p ≠ 2 := by omega
      have hp3 : p ≠ 3 := by omega
      exact Nat.Prime.five_le_of_ne_two_of_ne_three hp hp2 hp3
    by_cases hp5 : p = 5
    · subst p
      simpa using section14_log_div_add_one_five_lt_three
    · have hp5lt : 5 < p := lt_of_le_of_ne hp5le (Ne.symm hp5)
      have h5mem : (5 : ℝ) ∈ Set.Ici (5 : ℝ) := by simp
      have hpmem : (p : ℝ) ∈ Set.Ici (5 : ℝ) := by
        show (5 : ℝ) ≤ p
        exact_mod_cast hp5le
      exact lt_trans
        (section14_strictAntiOn_log_div_add_one h5mem hpmem (by exact_mod_cast hp5lt))
        section14_log_div_add_one_five_lt_three
  · have hq2 : q ≠ 2 := by omega
    have hq5 : 5 ≤ q := Nat.Prime.five_le_of_ne_two_of_ne_three hq hq2 hq3
    have hqmem : (q : ℝ) ∈ Set.Ici (5 : ℝ) := by
      show (5 : ℝ) ≤ q
      exact_mod_cast hq5
    have hpmem : (p : ℝ) ∈ Set.Ici (5 : ℝ) := by
      show (5 : ℝ) ≤ p
      exact_mod_cast (le_trans hq5 hqp.le)
    exact section14_strictAntiOn_log_div_add_one hqmem hpmem (by exact_mod_cast hqp)

public theorem section14_pow_gt_pow_of_prime_lt {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (h2q : 2 < q) (hqp : q < p) :
    q ^ (p + 1) > p ^ (q + 1) := by
  have hf := section14_log_div_add_one_prime_lt hp hq h2q hqp
  have hcross :
      Real.log (p : ℝ) * ((q : ℝ) + 1) <
        Real.log (q : ℝ) * ((p : ℝ) + 1) :=
    (div_lt_div_iff₀ (by positivity : (0 : ℝ) < (p : ℝ) + 1)
      (by positivity : (0 : ℝ) < (q : ℝ) + 1)).mp hf
  have hlogpow :
      Real.log ((p : ℝ) ^ (q + 1)) < Real.log ((q : ℝ) ^ (p + 1)) := by
    rw [Real.log_pow, Real.log_pow]
    norm_num at hcross ⊢
    nlinarith
  have hreal : ((p : ℝ) ^ (q + 1)) < ((q : ℝ) ^ (p + 1)) :=
    (Real.log_lt_log_iff (pow_pos (by exact_mod_cast hp.pos) _)
      (pow_pos (by exact_mod_cast hq.pos) _)).mp hlogpow
  exact_mod_cast hreal

public theorem section14_geom_quotient_minus_one_cast {p q : ℕ}
    (hp2 : 2 ≤ p) (hqpos : 0 < q) :
    ((((p ^ q - 1) / (p - 1) - 1 : ℕ) : ℝ) =
      ((p : ℝ) ^ q - p) / ((p : ℝ) - 1)) := by
  let A : ℕ := (p ^ q - 1) / (p - 1)
  change (((A - 1 : ℕ) : ℝ) = ((p : ℝ) ^ q - p) / ((p : ℝ) - 1))
  have hAone : 1 ≤ A := by
    dsimp [A]
    rw [← Nat.geomSum_eq hp2 q]
    cases q with
    | zero => omega
    | succ n =>
        rw [Finset.sum_range_succ']
        simp
  have hAcast : (A : ℝ) = ((p : ℝ) ^ q - 1) / ((p : ℝ) - 1) := by
    dsimp [A]
    have hdvd : p - 1 ∣ p ^ q - 1 := Nat.sub_one_dvd_pow_sub_one p q
    rw [Nat.cast_div hdvd (by exact_mod_cast (Nat.sub_ne_zero_of_lt hp2))]
    have hpq1 : 1 ≤ p ^ q := by exact pow_pos (by omega : 0 < p) q
    rw [Nat.cast_sub hpq1, Nat.cast_sub (by omega : 1 ≤ p)]
    norm_num
  rw [Nat.cast_sub hAone, hAcast]
  have hpne : (p : ℝ) - 1 ≠ 0 := by
    have hpgt : (1 : ℝ) < p := by exact_mod_cast hp2
    linarith
  field_simp [hpne]
  ring_nf

public theorem section14_ratio_core_of_pow {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (h2q : 2 < q)
    (hqp : q < p) (hpow : q ^ (p + 1) > p ^ (q + 1)) :
    (((p : ℝ) ^ q - p) / ((p : ℝ) - 1)) / (q : ℝ) <
      (((q : ℝ) ^ p - q) / ((q : ℝ) - 1)) / (p : ℝ) := by
  have hpgt1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hqgt1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hqpR : (q : ℝ) < p := by exact_mod_cast hqp
  have hpowR : (p : ℝ) ^ (q + 1) < (q : ℝ) ^ (p + 1) := by exact_mod_cast hpow
  have hp_exp_gt_sq : (p : ℝ) ^ 2 < (p : ℝ) ^ (q + 1) :=
    pow_lt_pow_right₀ hpgt1 (by omega : 2 < q + 1)
  have hdiff_pos : 0 < (p : ℝ) ^ (q + 1) - (p : ℝ) ^ 2 := by nlinarith
  have hsq : (q : ℝ) ^ 2 < (p : ℝ) ^ 2 := by nlinarith
  have hdiff_lt :
      (p : ℝ) ^ (q + 1) - (p : ℝ) ^ 2 <
        (q : ℝ) ^ (p + 1) - (q : ℝ) ^ 2 := by
    nlinarith
  have hprod :
      ((q : ℝ) - 1) * ((p : ℝ) ^ (q + 1) - (p : ℝ) ^ 2) <
        ((p : ℝ) - 1) * ((q : ℝ) ^ (p + 1) - (q : ℝ) ^ 2) := by
    have hpq1 : (q : ℝ) - 1 < (p : ℝ) - 1 := by linarith
    exact mul_lt_mul hpq1 hdiff_lt.le hdiff_pos (by linarith : 0 ≤ (p : ℝ) - 1)
  rw [div_div, div_div]
  rw [div_lt_div_iff₀
    (mul_pos (by linarith : 0 < (p : ℝ) - 1) (by positivity : 0 < (q : ℝ)))
    (mul_pos (by linarith : 0 < (q : ℝ) - 1) (by positivity : 0 < (p : ℝ)))]
  ring_nf at hprod ⊢
  nlinarith

public theorem section14_ratio_ineq_of_bounds {p q u v : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (h2q : 2 < q)
    (hqp : q < p) (hu : u ≤ (p ^ q - 1) / (p - 1))
    (hv : v = (q ^ p - 1) / (q - 1))
    (hpow : q ^ (p + 1) > p ^ (q + 1)) :
    ((v - 1 : ℕ) : ℝ) / (p : ℝ) > ((u - 1 : ℕ) : ℝ) / (q : ℝ) := by
  have hcore := section14_ratio_core_of_pow hp hq h2q hqp hpow
  have hAcast := section14_geom_quotient_minus_one_cast (p := p) (q := q)
    hp.two_le hq.pos
  have hBcast := section14_geom_quotient_minus_one_cast (p := q) (q := p)
    hq.two_le hp.pos
  have hu_sub : u - 1 ≤ (p ^ q - 1) / (p - 1) - 1 :=
    Nat.sub_le_sub_right hu 1
  have hu_real :
      ((u - 1 : ℕ) : ℝ) / (q : ℝ) ≤
        (((p ^ q - 1) / (p - 1) - 1 : ℕ) : ℝ) / (q : ℝ) :=
    div_le_div_of_nonneg_right (by exact_mod_cast hu_sub) (by positivity)
  have hv_real :
      ((v - 1 : ℕ) : ℝ) / (p : ℝ) =
        ((((q ^ p - 1) / (q - 1) - 1 : ℕ) : ℝ) / (p : ℝ)) := by
    rw [hv]
  rw [hv_real, hBcast]
  refine lt_of_le_of_lt hu_real ?_
  rw [hAcast]
  exact hcore

public theorem section14_geom_sum_gt_mul_of_two_le {q n : ℕ}
    (hq2 : 2 ≤ q) (hn3 : 3 ≤ n) :
    (∑ k ∈ Finset.range n, q ^ k) > n * q := by
  refine Nat.le_induction ?base ?step n hn3
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    simp [pow_two]
    have hq2mul : 2 * q ≤ q * q := Nat.mul_le_mul_right q hq2
    omega
  · intro n hn3 ih
    rw [Finset.sum_range_succ, Nat.succ_mul]
    have hpow_ge : q ≤ q ^ n := by
      exact Nat.le_self_pow (n := n) (by omega : n ≠ 0) q
    have hsum_ge : n * q + 1 ≤ ∑ k ∈ Finset.range n, q ^ k := by omega
    omega

public theorem section14_geom_quotient_gt_mul_of_prime_lt {p q : ℕ}
    (hq : Nat.Prime q) (hqp : q < p) :
    (q ^ p - 1) / (q - 1) > p * q := by
  have hq2 : 2 ≤ q := hq.two_le
  have hp3 : 3 ≤ p := by omega
  have hsum := section14_geom_sum_gt_mul_of_two_le (q := q) (n := p) hq2 hp3
  simpa [Nat.geomSum_eq hq2 p] using hsum

public theorem section14_v_gt_pq_of_case_b_formula
    {G : Type u} [Group G] [Finite G]
    {Tmax D : Subgroup G} {p q v : ℕ}
    (hqp : q < p)
    (hcaseT : Section13.case_9_7_b_for_section13 Tmax D q p v)
    (hv : v = (q ^ p - 1) / (q - 1)) :
    v > p * q := by
  rcases hcaseT with ⟨_hDT, hq, _hp, _hcop, _hdiv⟩
  rw [hv]
  exact section14_geom_quotient_gt_mul_of_prime_lt hq hqp

public theorem section14_v_le_pq_of_real_squeeze {p q u v k : ℕ}
    (hp : 0 < p) (hq3 : 3 ≤ q) (hqp : q < p)
    (hu : 2 * q < u) (hv : 2 * p < v) (hk : 2 * p * v < k)
    (hineq :
      1 / (p : ℝ) + 1 / (q : ℝ) ≤
        ((p * q : ℕ) : ℝ) / (k : ℝ) +
          2 / (((p * q : ℕ) : ℝ)) +
          1 / (((u * q : ℕ) : ℝ)) +
          1 / (((v * p : ℕ) : ℝ))) :
    v ≤ p * q := by
  have hqpos : 0 < q := by omega
  have hupos : 0 < u := by omega
  have hvpos : 0 < v := by omega
  have hkpos : 0 < k := by omega
  have hpposR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqposR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hkposR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hpqposR : (0 : ℝ) < ((p * q : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hp hqpos
  have huqposR : (0 : ℝ) < ((u * q : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hupos hqpos
  have hvpposR : (0 : ℝ) < ((v * p : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hvpos hp
  have hsmall :
      2 / (((p * q : ℕ) : ℝ)) + 1 / (((u * q : ℕ) : ℝ)) +
          1 / (((v * p : ℕ) : ℝ)) < 1 / (q : ℝ) := by
    have hp_gt_qR : (q : ℝ) < p := by exact_mod_cast hqp
    have hu_gtR : (2 * q : ℝ) < u := by exact_mod_cast hu
    have hv_gtR : (2 * p : ℝ) < v := by exact_mod_cast hv
    have hterm1 :
        2 / (((p * q : ℕ) : ℝ)) < 2 / ((q : ℝ) * (q : ℝ)) := by
      rw [Nat.cast_mul]
      gcongr
    have hterm2 :
        1 / (((u * q : ℕ) : ℝ)) < 1 / (2 * (q : ℝ) * (q : ℝ)) := by
      rw [Nat.cast_mul]
      gcongr
    have hterm3 :
        1 / (((v * p : ℕ) : ℝ)) < 1 / (2 * (q : ℝ) * (q : ℝ)) := by
      rw [Nat.cast_mul]
      gcongr
      nlinarith
    have hsum_lt :
        2 / (((p * q : ℕ) : ℝ)) + 1 / (((u * q : ℕ) : ℝ)) +
            1 / (((v * p : ℕ) : ℝ)) <
          2 / ((q : ℝ) * (q : ℝ)) + 1 / (2 * (q : ℝ) * (q : ℝ)) +
            1 / (2 * (q : ℝ) * (q : ℝ)) := by
      nlinarith
    have hq3R : (3 : ℝ) ≤ q := by exact_mod_cast hq3
    have hbound :
        2 / ((q : ℝ) * (q : ℝ)) + 1 / (2 * (q : ℝ) * (q : ℝ)) +
            1 / (2 * (q : ℝ) * (q : ℝ)) ≤ 1 / (q : ℝ) := by
      field_simp [ne_of_gt hqposR]
      nlinarith
    exact lt_of_lt_of_le hsum_lt hbound
  have hmain_lt : 1 / (p : ℝ) < ((p * q : ℕ) : ℝ) / (k : ℝ) := by
    nlinarith
  have hk_lt : (k : ℝ) < (p : ℝ) * ((p * q : ℕ) : ℝ) := by
    field_simp [ne_of_gt hpposR, ne_of_gt hkposR] at hmain_lt ⊢
    nlinarith
  have hk_lt_nat : k < p * (p * q) := by exact_mod_cast hk_lt
  have hv_bound : 2 * p * v < p * (p * q) := lt_trans hk hk_lt_nat
  have hv_lt : v < p * q := by
    nlinarith [show 0 < p by exact hp]
  exact Nat.le_of_lt hv_lt


end CFSG.Section14
