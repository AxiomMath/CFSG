module

public import CFSG.Quasithin.Vol2.Ch11SecJDick1
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecJ

open Matrix
open scoped Matrix

variable {F : Type*} [Field F]

@[expose] def IsAniso (y : GL (Fin 2) F) : Prop :=
  ∀ a b : F, ¬ (a = 0 ∧ b = 0) →
    (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • (y : Matrix (Fin 2) (Fin 2) F)).det ≠ 0

theorem IsAniso.ne_smul {y : GL (Fin 2) F} (hy : IsAniso y) (c : F) :
    (y : Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F) := by
  intro h
  apply hy c (-1) (fun h' => by simp at h')
  rw [h, neg_smul, one_smul, add_neg_cancel, Matrix.det_zero]

theorem IsAniso.eq_zero_or_eq_zero {y : GL (Fin 2) F} (hy : IsAniso y) {a b c d : F}
    (h : (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • (y : Matrix (Fin 2) (Fin 2) F)) *
      (c • (1 : Matrix (Fin 2) (Fin 2) F) + d • (y : Matrix (Fin 2) (Fin 2) F)) = 0) :
    (a = 0 ∧ b = 0) ∨ (c = 0 ∧ d = 0) := by
  by_contra hne
  push Not at hne
  have h1 : ¬ (a = 0 ∧ b = 0) := fun h' => by
    obtain ⟨h1, h2⟩ := hne
    exact h1 h'.1 h'.2
  have h2 : ¬ (c = 0 ∧ d = 0) := fun h' => by
    obtain ⟨-, h2⟩ := hne
    exact h2 h'.1 h'.2
  have h3 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_zero] at h3
  exact (mul_ne_zero (hy a b h1) (hy c d h2)) h3

theorem conj_eq_or_eq {y h : GL (Fin 2) F} (hy : IsAniso y)
    (hc : (h * y * h⁻¹) * y = y * (h * y * h⁻¹)) :
    ((h * y * h⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (y : Matrix (Fin 2) (Fin 2) F) ∨
      ((h * y * h⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (y : Matrix (Fin 2) (Fin 2) F).trace • (1 : Matrix (Fin 2) (Fin 2) F) -
          (y : Matrix (Fin 2) (Fin 2) F) := by
  set Y : Matrix (Fin 2) (Fin 2) F := (y : Matrix (Fin 2) (Fin 2) F) with hY
  set Y' : Matrix (Fin 2) (Fin 2) F :=
    ((h * y * h⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hY'
  have hc' : Y' * Y = Y * Y' := by
    have := congrArg Units.val hc
    simpa [hY, hY'] using this
  have htr : Y'.trace = Y.trace := by
    rw [hY', Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, Units.inv_mul, one_mul]
  have hdet : Y'.det = Y.det := by
    rw [hY', Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm,
      ← mul_assoc, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one, one_mul]
  obtain ⟨a, b, hab⟩ := exists_eq_of_commute (hy.ne_smul) hc'
  have hprod : (Y' - Y) * (Y' + Y - Y.trace • 1) = 0 := by
    have e1 := mul_self_eq_trace Y
    have e2 := mul_self_eq_trace Y'
    rw [htr, hdet] at e2
    calc (Y' - Y) * (Y' + Y - Y.trace • 1) =
          Y' * Y' - Y * Y + (Y' * Y - Y * Y') - Y.trace • Y' + Y.trace • Y := by
          rw [sub_mul, mul_sub, mul_sub, mul_add, mul_add, Matrix.mul_smul, Matrix.mul_smul,
            Matrix.mul_one, Matrix.mul_one]
          abel
      _ = 0 := by rw [e1, e2, hc', sub_self]; abel
  have hf1 : Y' - Y = a • (1 : Matrix (Fin 2) (Fin 2) F) + (b - 1) • Y := by
    rw [hab, sub_smul, one_smul]
    abel
  have hf2 : Y' + Y - Y.trace • 1 =
      (a - Y.trace) • (1 : Matrix (Fin 2) (Fin 2) F) + (b + 1) • Y := by
    rw [hab, sub_smul, add_smul, one_smul]
    abel
  rw [hf1, hf2] at hprod
  rcases hy.eq_zero_or_eq_zero hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    have : b = 1 := by linear_combination h2
    rw [hab, h1, this, zero_smul, zero_add, one_smul]
  · right
    have e1 : a = Y.trace := by linear_combination h1
    have e2 : b = -1 := by linear_combination h2
    rw [hab, e1, e2, neg_smul, one_smul, sub_eq_add_neg]

theorem commute_of_conj_commute {y h : GL (Fin 2) F} (hy : IsAniso y) (hodd : Odd (orderOf h))
    (hc : (h * y * h⁻¹) * y = y * (h * y * h⁻¹)) : h * y = y * h := by
  have hH : (h : Matrix (Fin 2) (Fin 2) F) * ((h⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : h ^ 2 * y * (h ^ 2)⁻¹ = y := by
    have hsq : h ^ 2 * y * (h ^ 2)⁻¹ = h * (h * y * h⁻¹) * h⁻¹ := by
      rw [pow_two, _root_.mul_inv_rev]
      group
    rcases conj_eq_or_eq hy hc with e | e
    · have e' : h * y * h⁻¹ = y := Units.ext e
      rw [hsq, e', e']
    · apply Units.ext
      rw [hsq, Units.val_mul, Units.val_mul, e, mul_sub, sub_mul, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, hH, ← Units.val_mul, ← Units.val_mul, e]
      abel
  have hcomm2 : Commute (h ^ 2) y := by
    show h ^ 2 * y = y * h ^ 2
    calc h ^ 2 * y = h ^ 2 * y * (h ^ 2)⁻¹ * h ^ 2 := by group
      _ = y * h ^ 2 := by rw [h2]
  obtain ⟨k, hk⟩ := hodd
  have hpow : h = (h ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf h + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [hpow]
  exact (hcomm2.pow_left (k + 1)).eq

theorem IsAniso.not_commute_upper {y h : GL (Fin 2) F} (hy : IsAniso y)
    (h10 : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (hd : (h : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ (h : Matrix (Fin 2) (Fin 2) F) 1 1)
    (hc : h * y = y * h) : False := by
  have hc' : (h : Matrix (Fin 2) (Fin 2) F) * (y : Matrix (Fin 2) (Fin 2) F) =
      (y : Matrix (Fin 2) (Fin 2) F) * (h : Matrix (Fin 2) (Fin 2) F) := by
    rw [← Units.val_mul, hc, Units.val_mul]
  obtain ⟨a, b, hab⟩ := exists_eq_of_commute hy.ne_smul hc'
  have heq : (a - (h : Matrix (Fin 2) (Fin 2) F) 0 0) • (1 : Matrix (Fin 2) (Fin 2) F) +
      b • (y : Matrix (Fin 2) (Fin 2) F) =
      (h : Matrix (Fin 2) (Fin 2) F) - (h : Matrix (Fin 2) (Fin 2) F) 0 0 • 1 := by
    rw [hab, sub_smul]
    abel
  have hdet : ((h : Matrix (Fin 2) (Fin 2) F) -
      (h : Matrix (Fin 2) (Fin 2) F) 0 0 • (1 : Matrix (Fin 2) (Fin 2) F)).det = 0 := by
    rw [Matrix.det_fin_two]
    simp [h10]
  by_cases hz : a - (h : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 ∧ b = 0
  · apply hd
    have e : (h : Matrix (Fin 2) (Fin 2) F) = (h : Matrix (Fin 2) (Fin 2) F) 0 0 • 1 := by
      have h1 := heq
      rw [hz.1, hz.2, zero_smul, zero_smul, add_zero] at h1
      exact (sub_eq_zero.1 h1.symm)
    have h11 := congrFun (congrFun e 1) 1
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h11
    exact h11.symm
  · exact hy _ _ hz (heq ▸ hdet)

end CFSG.Quasithin.Vol2.Ch11.SecJ
