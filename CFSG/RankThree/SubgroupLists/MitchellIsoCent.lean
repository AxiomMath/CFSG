module

public import CFSG.RankThree.SubgroupLists.MitchellFrame
public import CFSG.RankThree.SubgroupLists.MitchellIsotropic
public import CFSG.RankThree.SubgroupLists.MitchellWeight
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

theorem quad_sq_eq_zero_of_mem_isoCent {g : GL V₄ K} (hg : g ∈ isoCent K) :
    ((g : Matrix V₄ V₄ K) * (g : Matrix V₄ V₄ K) -
      (leviBlock (g : Matrix V₄ V₄ K)).trace • (g : Matrix V₄ V₄ K) + 1) ^ 2 = 0 := by
  obtain ⟨hl, e1, e2, e3, e4⟩ := entries_of_commute_isoStd hg.2
  have hdet := det_leviBlock hg
  rw [leviBlock, Matrix.det_fin_two_of] at hdet
  set M := (g : Matrix V₄ V₄ K)
  have htr : (leviBlock M).trace = M (Sum.inl 0) (Sum.inl 0) + M (Sum.inl 1) (Sum.inl 1) := by
    simp [leviBlock, Matrix.trace_fin_two]
  set S := M * M - (leviBlock M).trace • M + 1 with hS
  have hcol : ∀ (a : V₄) (j : Fin 2), S a (Sum.inl j) = 0 := by
    intro a j
    rcases a with i | i <;> fin_cases i <;> fin_cases j <;>
      simp [hS, htr, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.one_apply,
        hl] <;>
      first | linear_combination | linear_combination -hdet
  have hrow : ∀ (i : Fin 2) (b : V₄), S (Sum.inr i) b = 0 := by
    intro i b
    rcases b with j | j
    · exact hcol _ j
    fin_cases i <;> fin_cases j <;>
      simp [hS, htr, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.one_apply,
        hl, e1, e2, e3, e4] <;>
      first | linear_combination | linear_combination -hdet
  rw [sq]
  ext a b
  simp [Matrix.mul_apply, Fintype.sum_sum_type, hcol, hrow]

theorem exists_isoFrame (h2 : (2 : K) ≠ 0) {r : Matrix V₄ V₄ K}
    (hrM : r ∈ (cliffSpace : Submodule K _)) (hrr : cliffB r r = 0) (hr0 : r ≠ 0) :
    ∃ k ∈ StatedSp 2 K, ∀ g : GL V₄ K, g ∈ StatedSp 2 K →
      (g : Matrix V₄ V₄ K) * r = r * (g : Matrix V₄ V₄ K) →
      frameHom (RingHom.id K) k g ∈ isoCent K := by
  obtain ⟨k, hkS, b, hb, hkr⟩ := exists_conj_eq_smul_isoStd h2 hrM hrr hr0
  refine ⟨k, hkS, fun g hgS hgr => Subgroup.mem_inf.mpr ⟨frameHom_mem_statedSp _ hkS hgS, ?_⟩⟩
  rw [mem_matCent, coe_frameHom, frameMat]
  set Ki : Matrix V₄ V₄ K := ((k⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) with hKi
  set Km : Matrix V₄ V₄ K := (k : Matrix V₄ V₄ K) with hKm
  set X : Matrix V₄ V₄ K := (g : Matrix V₄ V₄ K)
  have hmap : X.map (RingHom.id K) = X := by
    ext i j
    simp
  rw [hmap]
  have hKK : Km * Ki = 1 := by rw [hKm, hKi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have key : Ki * X * Km * (b • isoStd) = (b • isoStd) * (Ki * X * Km) := by
    rw [← hkr]
    calc Ki * X * Km * (Ki * r * Km) = Ki * (X * r) * Km := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Km Ki, hKK, Matrix.one_mul]
      _ = Ki * (r * X) * Km := by rw [hgr]
      _ = Ki * r * Km * (Ki * X * Km) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Km Ki, hKK, Matrix.one_mul]
  rw [Matrix.mul_smul, Matrix.smul_mul] at key
  exact smul_right_injective _ hb key

theorem false_of_isoCent_conj_pow {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {G : Subgroup (GL V₄ (ZMod p))} (hU0 : ∀ x ∈ G, IsSqZero x → x = 1)
    {g h : GL V₄ (ZMod p)} (hgG : g ∈ G) (hgC : g ∈ isoCent (ZMod p))
    (hhC : h ∈ isoCent (ZMod p)) (hg1 : g ≠ 1)
    (hgu : (leviBlock ((g : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p))).trace = 2)
    {k : ℕ} (hk : h ^ k = 1) (hpk : ¬ p ∣ k) {m : ℕ} (hconj : h * g * h⁻¹ = g ^ m)
    (hm : ((m : ZMod p)) ^ 2 ≠ 1) : False := by
  have hne : ∀ n : ℕ, n < p → n ≠ 0 → ((n : ℕ) : ZMod p) ≠ 0 := fun n hn hn0 h0 =>
    hn0 (Nat.eq_zero_of_dvd_of_lt ((CharP.cast_eq_zero_iff (ZMod p) p n).mp h0) hn)
  have h2 : (2 : ZMod p) ≠ 0 := by exact_mod_cast hne 2 (by omega) (by norm_num)
  have h3 : (3 : ZMod p) ≠ 0 := by exact_mod_cast hne 3 (by omega) (by norm_num)
  have hq := quad_sq_eq_zero_of_mem_isoCent hgC
  rw [hgu] at hq
  have hN : ((g : Matrix V₄ V₄ (ZMod p)) - 1) ^ 4 = 0 := by
    have e : ((g : Matrix V₄ V₄ (ZMod p)) - 1) ^ 2 = (g : Matrix V₄ V₄ (ZMod p)) * g -
        (2 : ZMod p) • (g : Matrix V₄ V₄ (ZMod p)) + 1 := by
      rw [two_smul, sq]
      noncomm_ring
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, e]
    exact hq
  have hMk : (h : Matrix V₄ V₄ (ZMod p)) ^ k = 1 := by
    rw [← Units.val_pow_eq_pow_val, hk, Units.val_one]
  have hqh := quad_eq_zero_of_pow_eq_one_of_sq hMk hpk (quad_sq_eq_zero_of_mem_isoCent hhC)
  have hconj' : (h : Matrix V₄ V₄ (ZMod p)) * g = (g : Matrix V₄ V₄ (ZMod p)) ^ m * h := by
    rw [← Units.val_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← hconj,
      inv_mul_cancel_right]
  exact hg1 (hU0 g hgG (sub_one_mul_self_eq_zero_of_conj_pow h2 h3 hN hconj' hqh hm))

end CFSG.RankThree.SubgroupLists
