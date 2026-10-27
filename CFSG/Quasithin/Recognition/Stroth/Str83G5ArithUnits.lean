module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5ArithLab
public import CFSG.Quasithin.Recognition.Stroth.Str83G5ArithBasic

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

public section

namespace CFSG.Quasithin.Stroth.G5

variable {n : ℕ}

section Helpers

variable {k₀ m₀ T : ZMod (2 ^ n - 1)}

private theorem nontrivial_of_three_le (h3 : 3 ≤ n) : Nontrivial (ZMod (2 ^ n - 1)) :=
  nontrivial_of_ne _ _ (two_ne_zero' h3)

private theorem mPow_zero_vec (t : ℤ) : mPow k₀ m₀ t (0 : Coord n) = 0 := by
  simpa using mPow_smul k₀ m₀ t 0 (0 : Coord n)

private theorem smul_eq_zero_of_smul_mPow {a : ZMod (2 ^ n - 1)} {v : Coord n} (t : ℤ)
    (h : a • mPow k₀ m₀ t v = 0) : a • v = 0 := by
  apply mPow_injective k₀ m₀ t
  rw [mPow_smul, h, mPow_zero_vec]

private theorem psi_ne_neg (h3 : 3 ≤ n) (m₀ : ZMod (2 ^ n - 1)) : psi m₀ ≠ -psi m₀ := by
  intro h
  have h1 := congrArg Prod.fst h
  simp only [psi_fst, Prod.fst_neg] at h1
  exact two_ne_zero' h3 (by linear_combination h1)

private theorem chi_ne_neg (h3 : 3 ≤ n) (k₀ : ZMod (2 ^ n - 1)) : chi k₀ ≠ -chi k₀ := by
  intro h
  have h1 := congrArg Prod.snd h
  simp only [chi_snd, Prod.snd_neg] at h1
  exact two_ne_zero' h3 (by linear_combination h1)

private theorem mPow_one_psi_ne (h3 : 3 ≤ n) (hm : IsUnit m₀) :
    mPow k₀ m₀ 1 (psi m₀) ≠ -psi m₀ := by
  intro h
  have h1 := mPow_one_psi_add k₀ m₀
  rw [h, neg_add_cancel] at h1
  have h2 : 2 * m₀ = 0 := (smul_chi_eq_zero_iff k₀ (2 * m₀)).mp h1.symm
  exact two_ne_zero' h3 (hm.mul_left_eq_zero.mp h2)

private theorem mPow_one_chi_ne (h3 : 3 ≤ n) (hk : IsUnit k₀) (hm : IsUnit m₀) :
    mPow k₀ m₀ 1 (chi k₀) ≠ -chi k₀ := by
  intro h
  haveI := nontrivial_of_three_le h3
  have h1 := mPow_one_chi_add k₀ m₀
  rw [h, neg_add_cancel] at h1
  have h2 : mPow k₀ m₀ 1 (psi m₀) = 0 :=
    ((isUnit_two (by omega)).mul hk).smul_eq_zero.mp h1.symm
  have h4 := congrArg Prod.snd h2
  simp only [mPow_one_snd, psi_fst, psi_snd, Prod.snd_zero] at h4
  exact hm.ne_zero (by linear_combination h4)

private theorem mPow_rec_T (hT : 4 * k₀ * m₀ - 2 = T) (t : ℤ) (v : Coord n) :
    mPow k₀ m₀ (t + 2) v = T • mPow k₀ m₀ (t + 1) v - mPow k₀ m₀ t v := by
  subst hT
  exact mPow_add_two k₀ m₀ t v

private theorem mPow_two_T (hT : 4 * k₀ * m₀ - 2 = T) (v : Coord n) :
    mPow k₀ m₀ 2 v = T • mPow k₀ m₀ 1 v - v := by
  subst hT
  exact mPow_two k₀ m₀ v

private theorem mPow_one_one (v : Coord n) :
    mPow k₀ m₀ 1 (mPow k₀ m₀ 1 v) = mPow k₀ m₀ 2 v :=
  (mPow_add k₀ m₀ 1 1 v).symm

private theorem mPow_two_add_one (v : Coord n) :
    mPow k₀ m₀ 2 v + mPow k₀ m₀ 1 v = mPow k₀ m₀ 1 (mPow k₀ m₀ 1 v + v) := by
  rw [mPow_add_vec, mPow_one_one]

private theorem mPow_three_add (hT : 4 * k₀ * m₀ - 2 = T) (v : Coord n) :
    mPow k₀ m₀ 3 v + v = (T - 1) • (mPow k₀ m₀ 2 v + mPow k₀ m₀ 1 v) := by
  have h3 : mPow k₀ m₀ 3 v = T • mPow k₀ m₀ 2 v - mPow k₀ m₀ 1 v := mPow_rec_T hT 1 v
  rw [h3, mPow_two_T hT v]
  module

private theorem mPow_four_add (hT : 4 * k₀ * m₀ - 2 = T) (v : Coord n) :
    mPow k₀ m₀ 4 v + v = (T ^ 2 - 2) • mPow k₀ m₀ 2 v := by
  have h4 : mPow k₀ m₀ 4 v = T • mPow k₀ m₀ 3 v - mPow k₀ m₀ 2 v := mPow_rec_T hT 2 v
  have h3 : mPow k₀ m₀ 3 v = T • mPow k₀ m₀ 2 v - mPow k₀ m₀ 1 v := mPow_rec_T hT 1 v
  have h2 := mPow_two_T hT v
  rw [h4, h3]
  linear_combination (norm := module) h2

private theorem T_eq_zero_of_psi_two (hT : 4 * k₀ * m₀ - 2 = T) (hm : IsUnit m₀)
    (h : mPow k₀ m₀ 2 (psi m₀) = -psi m₀) : T = 0 := by
  rw [mPow_two_T hT, sub_eq_neg_self] at h
  have h2 := congrArg Prod.snd h
  simp only [Prod.smul_snd, smul_eq_mul, mPow_one_snd, psi_fst, psi_snd, Prod.snd_zero] at h2
  have h3 : T * m₀ = 0 := by linear_combination h2
  exact hm.mul_left_eq_zero.mp h3

private theorem T_eq_zero_of_chi_two (hT : 4 * k₀ * m₀ - 2 = T)
    (h : mPow k₀ m₀ 2 (chi k₀) = -chi k₀) : T = 0 := by
  rw [mPow_two_T hT, sub_eq_neg_self] at h
  exact (smul_chi_eq_zero_iff k₀ T).mp (smul_eq_zero_of_smul_mPow 1 h)

private theorem T_eq_one_of_psi_three (hT : 4 * k₀ * m₀ - 2 = T) (h3 : 3 ≤ n) (hm : IsUnit m₀)
    (h : mPow k₀ m₀ 3 (psi m₀) = -psi m₀) : T = 1 := by
  have h1 : mPow k₀ m₀ 3 (psi m₀) + psi m₀ =
      ((T - 1) * (2 * m₀)) • mPow k₀ m₀ 1 (chi k₀) := by
    rw [mPow_three_add hT, mPow_two_add_one, mPow_one_psi_add, mPow_smul, ← mul_smul]
  rw [h, neg_add_cancel] at h1
  have h2 := (smul_chi_eq_zero_iff k₀ _).mp (smul_eq_zero_of_smul_mPow 1 h1.symm)
  exact sub_eq_zero.mp (((isUnit_two (by omega)).mul hm).mul_left_eq_zero.mp h2)

private theorem T_eq_one_of_chi_three (hT : 4 * k₀ * m₀ - 2 = T) (h3 : 3 ≤ n) (hk : IsUnit k₀)
    (h : mPow k₀ m₀ 3 (chi k₀) = -chi k₀) : T = 1 := by
  have h1 : mPow k₀ m₀ 3 (chi k₀) + chi k₀ =
      ((T - 1) * (2 * k₀)) • mPow k₀ m₀ 2 (psi m₀) := by
    rw [mPow_three_add hT, mPow_two_add_one, mPow_one_chi_add, mPow_smul, ← mul_smul,
      mPow_one_one]
  rw [h, neg_add_cancel] at h1
  have h2 := (smul_psi_eq_zero_iff m₀ _).mp (smul_eq_zero_of_smul_mPow 2 h1.symm)
  exact sub_eq_zero.mp (((isUnit_two (by omega)).mul hk).mul_left_eq_zero.mp h2)

private theorem sq_eq_two_of_psi_four (hT : 4 * k₀ * m₀ - 2 = T)
    (h : mPow k₀ m₀ 4 (psi m₀) = -psi m₀) : T ^ 2 = 2 := by
  have h1 := mPow_four_add hT (psi m₀)
  rw [h, neg_add_cancel] at h1
  exact sub_eq_zero.mp ((smul_psi_eq_zero_iff m₀ _).mp (smul_eq_zero_of_smul_mPow 2 h1.symm))

private theorem sq_eq_two_of_chi_four (hT : 4 * k₀ * m₀ - 2 = T)
    (h : mPow k₀ m₀ 4 (chi k₀) = -chi k₀) : T ^ 2 = 2 := by
  have h1 := mPow_four_add hT (chi k₀)
  rw [h, neg_add_cancel] at h1
  exact sub_eq_zero.mp ((smul_chi_eq_zero_iff k₀ _).mp (smul_eq_zero_of_smul_mPow 2 h1.symm))

private theorem one_ne_sq_two (h3 : 3 ≤ n) (h1 : T = 1) (h2 : T ^ 2 = 2) : False := by
  haveI := nontrivial_of_three_le h3
  rw [h1] at h2
  exact one_ne_zero (by linear_combination -h2 : (1 : ZMod (2 ^ n - 1)) = 0)

private theorem mPow_rec_zero (hT : 4 * k₀ * m₀ - 2 = T) (h0 : T = 0) (t : ℤ) (v : Coord n) :
    mPow k₀ m₀ (t + 2) v = -mPow k₀ m₀ t v := by
  rw [mPow_rec_T hT, h0, zero_smul, zero_sub]

private theorem T0_ne (hT : 4 * k₀ * m₀ - 2 = T) (h0 : T = 0) {v : Coord n} (hv : v ≠ -v)
    (hM : mPow k₀ m₀ 1 v ≠ -v) :
    mPow k₀ m₀ 3 v ≠ -v ∧ mPow k₀ m₀ 4 v ≠ -v ∧ mPow k₀ m₀ 5 v ≠ -v ∧
      mPow k₀ m₀ 7 v ≠ -v ∧ mPow k₀ m₀ 8 v ≠ -v := by
  have e2 : mPow k₀ m₀ 2 v = -v := mPow_rec_zero hT h0 0 v
  have e3 : mPow k₀ m₀ 3 v = -mPow k₀ m₀ 1 v := mPow_rec_zero hT h0 1 v
  have e4 : mPow k₀ m₀ 4 v = -mPow k₀ m₀ 2 v := mPow_rec_zero hT h0 2 v
  have e5 : mPow k₀ m₀ 5 v = -mPow k₀ m₀ 3 v := mPow_rec_zero hT h0 3 v
  have e6 : mPow k₀ m₀ 6 v = -mPow k₀ m₀ 4 v := mPow_rec_zero hT h0 4 v
  have e7 : mPow k₀ m₀ 7 v = -mPow k₀ m₀ 5 v := mPow_rec_zero hT h0 5 v
  have e8 : mPow k₀ m₀ 8 v = -mPow k₀ m₀ 6 v := mPow_rec_zero hT h0 6 v
  have hM1 : mPow k₀ m₀ 1 v ≠ v := by
    intro h
    apply hv
    rw [← e2, ← mPow_one_one, h, h]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [e3, neg_inj] at h
    exact hM1 h
  · rw [e4, e2, neg_neg] at h
    exact hv h
  · rw [e5, e3, neg_neg] at h
    exact hM h
  · rw [e7, e5, e3, neg_neg, neg_inj] at h
    exact hM1 h
  · rw [e8, e6, e4, e2, neg_neg, neg_neg] at h
    exact hv h

private theorem mPow_three_of_T_one (hT : 4 * k₀ * m₀ - 2 = T) (h1 : T = 1) (v : Coord n) :
    mPow k₀ m₀ 3 v = -v := by
  have h3 : mPow k₀ m₀ 3 v = T • mPow k₀ m₀ 2 v - mPow k₀ m₀ 1 v := mPow_rec_T hT 1 v
  rw [h3, mPow_two_T hT v, h1]
  module

private theorem T1_ne (hn : Odd n) (h3 : 3 ≤ n) (hT : 4 * k₀ * m₀ - 2 = T) (h1 : T = 1) :
    mPow k₀ m₀ 5 (chi k₀) ≠ -chi k₀ ∧ mPow k₀ m₀ 6 (chi k₀) ≠ -chi k₀ := by
  haveI := nontrivial_of_three_le h3
  have h3' := mPow_three_of_T_one hT h1
  constructor
  · intro h
    have h5 : mPow k₀ m₀ 5 (chi k₀) = -mPow k₀ m₀ 2 (chi k₀) := by
      rw [show (5 : ℤ) = 2 + 3 from rfl, mPow_add, h3', mPow_neg_vec]
    rw [h5, neg_inj] at h
    have h2 := mPow_two_T hT (chi k₀)
    rw [h1, one_smul, h] at h2
    have hM1 : mPow k₀ m₀ 1 (chi k₀) = chi k₀ + chi k₀ := (eq_sub_iff_add_eq.mp h2).symm
    have hM22 : mPow k₀ m₀ 2 (chi k₀) = mPow k₀ m₀ 1 (chi k₀) + mPow k₀ m₀ 1 (chi k₀) := by
      rw [← mPow_one_one, hM1, mPow_add_vec, hM1]
    have h4 : (3 : ZMod (2 ^ n - 1)) • chi k₀ = 0 := by
      linear_combination (norm := module) h - hM22 - (2 : ZMod (2 ^ n - 1)) • hM1
    exact (isUnit_three hn).ne_zero ((smul_chi_eq_zero_iff k₀ 3).mp h4)
  · intro h
    have h6 : mPow k₀ m₀ 6 (chi k₀) = chi k₀ := by
      rw [show (6 : ℤ) = 3 + 3 from rfl, mPow_add, h3' (mPow k₀ m₀ 3 (chi k₀)), h3', neg_neg]
    rw [h6] at h
    exact chi_ne_neg h3 k₀ h

end Helpers

theorem pairs30_cases (hn : Odd n) (h3 : 3 ≤ n) {k₀ m₀ : ZMod (2 ^ n - 1)} (hk : IsUnit k₀)
    (hm : IsUnit m₀) {r r' : ℕ} (hrr : (r, r') ∈ pairs30)
    (hψ : mPow k₀ m₀ r (psi m₀) = -psi m₀) (hχ : mPow k₀ m₀ r' (chi k₀) = -chi k₀) :
    (((r, r') = (2, 2) ∨ (r, r') = (2, 6)) ∧ 4 * k₀ * m₀ - 2 = 0) ∨
      ((r, r') = (3, 3) ∧ 4 * k₀ * m₀ - 2 = 1) ∨ (r, r') = (4, 4) := by
  obtain ⟨T, hT⟩ : ∃ T, 4 * k₀ * m₀ - 2 = T := ⟨_, rfl⟩
  rw [hT]
  have hψ1 := mPow_one_psi_ne (k₀ := k₀) h3 hm
  have hχ1 := mPow_one_chi_ne h3 hk hm
  have hχ0 : T = 0 → _ := fun h0 => T0_ne hT h0 (chi_ne_neg h3 k₀) hχ1
  have hψ0 : T = 0 → _ := fun h0 => T0_ne hT h0 (psi_ne_neg h3 m₀) hψ1
  have key : pairs30 = [(1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9),
      (1, 10), (2, 1), (3, 1), (4, 1), (5, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7),
      (2, 8), (3, 2), (4, 2), (5, 2), (3, 3), (3, 4), (3, 5), (3, 6), (4, 3), (4, 4)] := by
    decide
  rw [key] at hrr
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrr
  rcases hrr with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals first | exact absurd hψ hψ1 | exact absurd hχ hχ1 | skip
  · exact Or.inl ⟨Or.inl rfl, T_eq_zero_of_psi_two hT hm hψ⟩
  · exact absurd hχ (hχ0 (T_eq_zero_of_psi_two hT hm hψ)).1
  · exact absurd hχ (hχ0 (T_eq_zero_of_psi_two hT hm hψ)).2.1
  · exact absurd hχ (hχ0 (T_eq_zero_of_psi_two hT hm hψ)).2.2.1
  · exact Or.inl ⟨Or.inr rfl, T_eq_zero_of_psi_two hT hm hψ⟩
  · exact absurd hχ (hχ0 (T_eq_zero_of_psi_two hT hm hψ)).2.2.2.1
  · exact absurd hχ (hχ0 (T_eq_zero_of_psi_two hT hm hψ)).2.2.2.2
  · exact absurd hψ (hψ0 (T_eq_zero_of_chi_two hT hχ)).1
  · exact absurd hψ (hψ0 (T_eq_zero_of_chi_two hT hχ)).2.1
  · exact absurd hψ (hψ0 (T_eq_zero_of_chi_two hT hχ)).2.2.1
  · exact Or.inr (Or.inl ⟨rfl, T_eq_one_of_psi_three hT h3 hm hψ⟩)
  · exact (one_ne_sq_two h3 (T_eq_one_of_psi_three hT h3 hm hψ) (sq_eq_two_of_chi_four hT hχ)).elim
  · exact absurd hχ (T1_ne hn h3 hT (T_eq_one_of_psi_three hT h3 hm hψ)).1
  · exact absurd hχ (T1_ne hn h3 hT (T_eq_one_of_psi_three hT h3 hm hψ)).2
  · exact (one_ne_sq_two h3 (T_eq_one_of_chi_three hT h3 hk hχ) (sq_eq_two_of_psi_four hT hψ)).elim
  · exact Or.inr (Or.inr rfl)

end CFSG.Quasithin.Stroth.G5

end
