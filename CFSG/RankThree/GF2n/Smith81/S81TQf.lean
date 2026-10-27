module

public import CFSG.RankThree.GF2n.Smith81.S81E7Form
public import CFSG.RankThree.GF2n.Smith81.S81TDefs

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.MinuscT

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley


section Qf

variable {K : Type} [Field K] [CharP K 2]

theorem beta_tOp_selfAdj {S : List Rt} (hS : SOrth S) (u w : V K) :
    beta (tOp K S u) w = beta u (tOp K S w) := by
  have h := E_isometry (K := K) (tS_mem (K := K) S) u (tOp K S w)
  rw [tS_val] at h
  have hww : tOp K S (tOp K S w) = w := by
    rw [← Module.End.mul_apply, tOp_mul_self (K := K) hS, Module.End.one_apply]
  rw [hww] at h
  exact h

theorem beta_tOp_add {S : List Rt} (hS : SOrth S) (u w : V K) :
    beta (tOp K S (u + w)) (u + w) = beta (tOp K S u) u + beta (tOp K S w) w := by
  have hc : beta (tOp K S w) u = beta (tOp K S u) w := by
    rw [beta_tOp_selfAdj hS w u]
    exact beta_comm _ _
  have h2 : beta (tOp K S u) w + beta (tOp K S u) w = 0 :=
    add_self_eq_zero_of_charTwo (K := K) _
  rw [map_add, beta_add_left, beta_add_right, beta_add_right, hc]
  linear_combination h2

theorem aux_beta_tOp_single {S : List Rt} (hS : SOrth S) (a : Fin e7Data.d) :
    beta (tOp K S (Finsupp.single a 1)) (Finsupp.single a 1) = (cntW S a (-(e7Data.wt a)) : K) := by
  unfold beta
  rw [Finset.sum_eq_single (opp a)]
  · rw [Finsupp.single_apply, if_pos (opp_opp a).symm, mul_one, tOp_single_apply hS.1, wt_opp]
  · intro b _ hb
    have hne : ¬ (a = opp b) := by
      intro h
      exact hb (by rw [h, opp_opp])
    rw [Finsupp.single_apply, if_neg hne, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem aux_beta_tOp_sum {S : List Rt} (hS : SOrth S) (v : V K) :
    beta (tOp K S v) v = ∑ a, (v a) ^ 2 * (cntW S a (-(e7Data.wt a)) : K) := by
  refine Finsupp.induction_linear v ?_ ?_ ?_
  · simp [beta]
  · intro f g hf hg
    rw [beta_tOp_add hS f g, hf, hg, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Finsupp.add_apply]
    rw [CharTwo.add_sq]
    ring
  · intro a b
    rw [← Finsupp.smul_single_one, map_smul, beta_smul_left, beta_smul_right,
      aux_beta_tOp_single hS a, Finset.sum_eq_single a]
    · simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
      ring
    · intro x _ hx
      simp [Finsupp.single_apply, Ne.symm hx]
    · intro h
      exact absurd (Finset.mem_univ a) h

theorem beta_NOp {S : List Rt} (hS : SOrth S) (v : V K) :
    beta (NOp K S v) v = ∑ a, (v a) ^ 2 * (cntW S a (-(e7Data.wt a)) : K) := by
  have hN : NOp K S v = tOp K S v - v := by
    rw [NOp_eq, LinearMap.sub_apply, Module.End.one_apply]
  have hq : beta (tOp K S v - v) v = beta (tOp K S v) v := by
    have h1 : beta (tOp K S v - v) v + beta v v = beta (tOp K S v) v := by
      rw [← beta_add_left, sub_add_cancel]
    rwa [beta_self v, add_zero] at h1
  rw [hN, hq]
  exact aux_beta_tOp_sum hS v

theorem natCast_eq_zero_of_mod_two {n : ℕ} (h : n % 2 = 0) : (n : K) = 0 :=
  (CharP.cast_eq_zero_iff K 2 n).2 (Nat.dvd_of_mod_eq_zero h)

theorem natCast_eq_one_of_mod_two {n : ℕ} (h : n % 2 = 1) : (n : K) = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
  push_cast
  rw [CharTwo.two_eq_zero, zero_mul, zero_add]

theorem beta_tOp_eq_zero_of_even {S : List Rt} (hS : SOrth S) {inL : Fin e7Data.d → Prop}
    (hpar : ∀ a, inL a → cntW S a (-(e7Data.wt a)) % 2 = 0) {v : V K} (hv : ∀ a, v a ≠ 0 → inL a) :
    beta (tOp K S v) v = 0 := by
  have h := beta_NOp (K := K) hS v
  rw [NOp_eq, LinearMap.sub_apply, Module.End.one_apply] at h
  have hq : beta (tOp K S v) v = ∑ a, (v a) ^ 2 * (cntW S a (-(e7Data.wt a)) : K) := by
    have h1 : beta (tOp K S v - v) v + beta v v = beta (tOp K S v) v := by
      rw [← beta_add_left, sub_add_cancel]
    rw [← h1, beta_self v, add_zero]
    exact h
  rw [hq]
  refine Finset.sum_eq_zero fun a _ => ?_
  by_cases hva : v a = 0
  · rw [hva]; ring
  · rw [natCast_eq_zero_of_mod_two (hpar a (hv a hva)), mul_zero]

theorem beta_tOp_single_eq_one {S : List Rt} (hS : SOrth S) {b : Fin e7Data.d}
    (hb : cntW S b (-(e7Data.wt b)) % 2 = 1) :
    beta (tOp K S (Finsupp.single b 1)) (Finsupp.single b 1) = 1 := by
  rw [aux_beta_tOp_single hS b, natCast_eq_one_of_mod_two hb]

end Qf

end CFSG.RankThree.GF2n.Smith81.MinuscT
