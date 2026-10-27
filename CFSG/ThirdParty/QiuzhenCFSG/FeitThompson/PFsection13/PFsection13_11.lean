module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection13.PFsection13_10

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 13: PFsection13_11
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section13

universe v
universe u

/-! ## (13.11) -/


/-! ## Numeric helpers for (13.11) -/

public theorem section13_geom_term_le_inv_sq
    {p q : ℕ} (hp : 3 ≤ p) (hq : 1 ≤ q) :
    ((q - 1 : ℕ) : ℝ) / ((q : ℝ) ^ p) ≤ 1 / ((q : ℝ) ^ 2) := by
  have hqone : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqnonneg : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hp3pow : (q : ℝ) ^ 3 ≤ (q : ℝ) ^ p := by
    exact pow_le_pow_right₀ hqone hp
  have hqsub_le : ((q - 1 : ℕ) : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.sub_le q 1
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  have hqppos : (0 : ℝ) < (q : ℝ) ^ p := by positivity
  calc
    ((q - 1 : ℕ) : ℝ) / ((q : ℝ) ^ p) ≤ (q : ℝ) / ((q : ℝ) ^ p) := by
      exact div_le_div_of_nonneg_right hqsub_le hqppos.le
    _ ≤ (q : ℝ) / ((q : ℝ) ^ 3) := by
      exact div_le_div_of_nonneg_left hqnonneg (by positivity) hp3pow
    _ = 1 / ((q : ℝ) ^ 2) := by
      field_simp [hqpos.ne']

public theorem section13_m_gt_eight_tenths
    {p q : ℕ} (hp : 3 ≤ p) (hq : 7 ≤ q) (m : ℝ)
    (hm : m = 1 - 1 / (((q - 1 : ℕ) : ℝ)) -
      ((q - 1 : ℕ) : ℝ) / ((q : ℝ) ^ p) +
        1 / ((((q - 1 : ℕ) : ℝ)) * ((q : ℝ) ^ p))) :
    (8 : ℝ) / 10 < m := by
  have hq1nat : 6 ≤ q - 1 := by omega
  have hq1R : (6 : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by exact_mod_cast hq1nat
  have hle1 : 1 / (((q - 1 : ℕ) : ℝ)) ≤ 1 / (6 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 6) hq1R
  have hqR : (7 : ℝ) ≤ q := by exact_mod_cast hq
  have hq2 : (49 : ℝ) ≤ (q : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((q : ℝ) - 7)]
  have hle2 : 1 / ((q : ℝ) ^ 2) ≤ 1 / (49 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 49) hq2
  have hleB : ((q - 1 : ℕ) : ℝ) / ((q : ℝ) ^ p) ≤ 1 / ((q : ℝ) ^ 2) :=
    section13_geom_term_le_inv_sq hp (le_trans (by norm_num) hq)
  have hposC : 0 ≤ 1 / ((((q - 1 : ℕ) : ℝ)) * ((q : ℝ) ^ p)) := by
    positivity
  nlinarith

public theorem section13_m_gt_seven_tenths
    {p q : ℕ} (hp : 3 ≤ p) (hq : 5 ≤ q) (m : ℝ)
    (hm : m = 1 - 1 / (((q - 1 : ℕ) : ℝ)) -
      ((q - 1 : ℕ) : ℝ) / ((q : ℝ) ^ p) +
        1 / ((((q - 1 : ℕ) : ℝ)) * ((q : ℝ) ^ p))) :
    (7 : ℝ) / 10 < m := by
  have hq1nat : 4 ≤ q - 1 := by omega
  have hq1R : (4 : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by exact_mod_cast hq1nat
  have hle1 : 1 / (((q - 1 : ℕ) : ℝ)) ≤ 1 / (4 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hq1R
  have hqR : (5 : ℝ) ≤ q := by exact_mod_cast hq
  have hq2 : (25 : ℝ) ≤ (q : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((q : ℝ) - 5)]
  have hle2 : 1 / ((q : ℝ) ^ 2) ≤ 1 / (25 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 25) hq2
  have hleB : ((q - 1 : ℕ) : ℝ) / ((q : ℝ) ^ p) ≤ 1 / ((q : ℝ) ^ 2) :=
    section13_geom_term_le_inv_sq hp (le_trans (by norm_num) hq)
  have hposC : 0 ≤ 1 / ((((q - 1 : ℕ) : ℝ)) * ((q : ℝ) ^ p)) := by
    positivity
  nlinarith

public theorem section13_sq_lt_three_pow_pred_of_five_le {p : ℕ} (hp : 5 ≤ p) :
    (p : ℝ) ^ 2 < (3 : ℝ) ^ (p - 1) := by
  have hp4 : 4 ≤ p := le_trans (by norm_num) hp
  have haux : ∀ k : ℕ, (((4 + k : ℕ) : ℝ) ^ 2 < (3 : ℝ) ^ (3 + k)) := by
    intro k
    induction k with
    | zero =>
        norm_num
    | succ k ih =>
        have hstep : (((4 + (k + 1) : ℕ) : ℝ) ^ 2 ≤
            3 * (((4 + k : ℕ) : ℝ) ^ 2)) := by
          norm_num [Nat.cast_add, Nat.cast_one]
          ring_nf
          nlinarith [sq_nonneg (k : ℝ)]
        calc
          ((4 + (k + 1) : ℕ) : ℝ) ^ 2 ≤
              3 * (((4 + k : ℕ) : ℝ) ^ 2) := hstep
          _ < 3 * ((3 : ℝ) ^ (3 + k)) := by nlinarith
          _ = (3 : ℝ) ^ (3 + (k + 1)) := by
            rw [show 3 + (k + 1) = (3 + k) + 1 by omega, pow_succ]
            ring
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp4
  have hk := haux k
  simpa [Nat.add_sub_cancel_left] using hk

public theorem section13_m_q_eq_three_gt_49_100
    {p q : ℕ} (hp : 5 ≤ p) (hqeq : q = 3) (m : ℝ)
    (hm : m = 1 - 1 / (((q - 1 : ℕ) : ℝ)) -
      ((q - 1 : ℕ) : ℝ) / ((q : ℝ) ^ p) +
        1 / ((((q - 1 : ℕ) : ℝ)) * ((q : ℝ) ^ p))) :
    (49 : ℝ) / 100 < m := by
  subst q
  have h3pow : (3 : ℝ) ^ 5 ≤ (3 : ℝ) ^ p := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hp
  have hle : (3 : ℝ) / (2 * (3 : ℝ) ^ p) ≤ 3 / (2 * (3 : ℝ) ^ 5) := by
    have hden : 2 * (3 : ℝ) ^ 5 ≤ 2 * (3 : ℝ) ^ p := by nlinarith
    exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3) (by positivity) hden
  have hle' : (3 : ℝ) / (2 * (3 : ℝ) ^ p) ≤ 1 / 162 := by
    norm_num at hle ⊢
    exact hle
  have hm' : m = (1 : ℝ) / 2 - 3 / (2 * (3 : ℝ) ^ p) := by
    rw [hm]
    norm_num [pow_succ]
    ring
  rw [hm']
  nlinarith

public theorem section13_m_q_eq_three_linear_bound
    {p q : ℕ} (hp : 5 ≤ p) (hqeq : q = 3) (m : ℝ)
    (hm : m = 1 - 1 / (((q - 1 : ℕ) : ℝ)) -
      ((q - 1 : ℕ) : ℝ) / ((q : ℝ) ^ p) +
        1 / ((((q - 1 : ℕ) : ℝ)) * ((q : ℝ) ^ p))) :
    ((p : ℝ) ^ 2 - 1) / 6 < (m * (p : ℝ) ^ 2) / 3 := by
  subst q
  have h3powpos : (0 : ℝ) < (3 : ℝ) ^ (p - 1) := by positivity
  have hm' : m = (1 : ℝ) / 2 - 3 / (2 * (3 : ℝ) ^ p) := by
    rw [hm]
    norm_num [pow_succ]
    ring
  have hm2 : m = (1 : ℝ) / 2 - 1 / (2 * (3 : ℝ) ^ (p - 1)) := by
    rw [hm']
    rw [show p = (p - 1) + 1 by omega]
    rw [pow_succ (3 : ℝ) (p - 1)]
    ring_nf
    rw [show 1 + (p - 1) - 1 = p - 1 by omega]
  have hexp : (p : ℝ) ^ 2 < (3 : ℝ) ^ (p - 1) :=
    section13_sq_lt_three_pow_pred_of_five_le hp
  rw [hm2]
  field_simp [h3powpos.ne']
  ring_nf
  nlinarith


/-- Proof placeholder for `theorem_13_11_statement`. -/
public theorem theorem_13_11
    {G : Type u}
    [Group G]
    [Finite G]
    (Smax Tmax W W1 W2 P Q U V C D : Subgroup G)
    (Sfam : Finset (Section1.ClassFunction Smax))
    (Tfam : Finset (Section1.ClassFunction Tmax))
    (τS : Section1.ClassFunction Smax →ₗ[ℂ] Section1.ClassFunction G)
    (τT : Section1.ClassFunction Tmax →ₗ[ℂ] Section1.ClassFunction G)
    (p q u v c d : ℕ)
    (m : ℝ)
    : hypothesis_13_1_sourceData Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d →
      theorem_13_10_hypothesis Smax P C Sfam p q u →
      m = 1 - 1 / ((q - 1 : ℕ) : ℝ) - ((q - 1 : ℕ) : ℝ) / ((q : ℝ) ^ p) +
        1 / (((q - 1 : ℕ) : ℝ) * ((q : ℝ) ^ p)) →
      (3 ≤ p → 7 ≤ q → (8 : ℝ) / 10 < m) ∧
        (3 ≤ p → 5 ≤ q → (7 : ℝ) / 10 < m) ∧
        (5 ≤ p → q = 3 → (49 : ℝ) / 100 < m ∧
          (u : ℝ) / (c : ℝ) > ((p : ℝ) ^ 2 - 1) / 6) := by
  intro hsource h10 hm
  constructor
  · intro hp hq
    exact section13_m_gt_eight_tenths hp hq m hm
  constructor
  · intro hp hq
    exact section13_m_gt_seven_tenths hp hq m hm
  · intro hp hqeq
    constructor
    · exact section13_m_q_eq_three_gt_49_100 hp hqeq m hm
    · have h10ineq := theorem_13_10 Smax Tmax W W1 W2 P Q U V C D
        Sfam Tfam τS τT p q u v c d m hsource h10 hm
      have hsource := section13_m_q_eq_three_linear_bound hp hqeq m hm
      have hineq : (u : ℝ) / (c : ℝ) > (m * (p : ℝ) ^ 2) / 3 := by
        simpa [hqeq] using h10ineq
      linarith
end CFSG.Section13
