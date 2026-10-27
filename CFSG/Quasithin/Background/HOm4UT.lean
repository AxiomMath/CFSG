module

public import CFSG.Quasithin.Background.HOm4Norm

public section

namespace CFSG.Quasithin.H.Om4

open Matrix

variable {K : Type} [Field K]

theorem mul_mul_transpose_entry (A M B : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    (A * M * Bᵀ) i j = A i 0 * (M 0 0 * B j 0 + M 0 1 * B j 1) +
      A i 1 * (M 1 0 * B j 0 + M 1 1 * B j 1) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  ring

theorem frM_mul (τ σ : K ≃+* K) : frM τ * frM σ = frM (τ * σ) :=
  MulEquiv.ext fun X => Multiplicative.toAdd.injective (by
    rw [MulAut.mul_apply, toAdd_frM, toAdd_frM, toAdd_frM, Matrix.map_map]
    rfl)

theorem frM_one : frM (1 : K ≃+* K) = 1 :=
  MulEquiv.ext fun X => Multiplicative.toAdd.injective (by
    rw [toAdd_frM, MulAut.one_apply]
    ext i j
    rfl)

theorem trM_frM (τ : K ≃+* K) : trM * frM τ = frM τ * trM :=
  MulEquiv.ext fun X => Multiplicative.toAdd.injective (by
    rw [MulAut.mul_apply, MulAut.mul_apply, toAdd_trM, toAdd_frM, toAdd_frM, toAdd_trM,
      Matrix.transpose_map])

@[expose] def IsNS (x : MulAut (VM K)) : Prop :=
  ∃ (A B : GL (Fin 2) K) (τ : K ≃+* K), x = lr A B * frM τ

theorem isNS_one : IsNS (1 : MulAut (VM K)) :=
  ⟨1, 1, 1, by rw [lr_one, frM_one, mul_one]⟩

theorem IsNS.mul {x y : MulAut (VM K)} (hx : IsNS x) (hy : IsNS y) : IsNS (x * y) := by
  obtain ⟨A, B, τ, rfl⟩ := hx
  obtain ⟨A', B', σ, rfl⟩ := hy
  refine ⟨A * GeneralLinearGroup.map τ.toRingHom A', B * GeneralLinearGroup.map τ.toRingHom B',
    τ * σ, ?_⟩
  rw [← lr_mul, ← frM_mul, mul_assoc, ← mul_assoc (frM τ), frM_lr]
  group

theorem IsNS.inv {x : MulAut (VM K)} (hx : IsNS x) : IsNS x⁻¹ := by
  obtain ⟨A, B, τ, rfl⟩ := hx
  refine ⟨GeneralLinearGroup.map τ⁻¹.toRingHom A⁻¹, GeneralLinearGroup.map τ⁻¹.toRingHom B⁻¹,
    τ⁻¹, ?_⟩
  have h1 : (frM τ)⁻¹ = frM τ⁻¹ := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, frM_mul, inv_mul_cancel, frM_one]
  rw [_root_.mul_inv_rev, h1, lr_inv, frM_lr]

theorem IsNS.pow {x : MulAut (VM K)} (hx : IsNS x) (k : ℕ) : IsNS (x ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact isNS_one
  | succ k ih => rw [pow_succ]; exact ih.mul hx

theorem not_isNS_trM : ¬ IsNS (trM : MulAut (VM K)) := by
  rintro ⟨A, B, τ, h⟩
  have key : ∀ X : Matrix (Fin 2) (Fin 2) K, Xᵀ =
      (A : Matrix (Fin 2) (Fin 2) K) * X.map τ * (B : Matrix (Fin 2) (Fin 2) K)ᵀ := by
    intro X
    have := congrArg (fun f : MulAut (VM K) => Multiplicative.toAdd (f (Multiplicative.ofAdd X))) h
    simpa only [toAdd_trM, MulAut.mul_apply, toAdd_lr, toAdd_frM, toAdd_ofAdd] using this
  have h1 := key !![1, 0; 0, 0]
  have h2 := key !![0, 1; 0, 0]
  have e00 := congrFun (congrFun h1 0) 0
  have e10 := congrFun (congrFun h1 1) 0
  have f10 := congrFun (congrFun h2 1) 0
  rw [mul_mul_transpose_entry] at e00 e10 f10
  simp at e00 e10 f10
  have hB : (B : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at e00
    exact one_ne_zero e00
  have hA : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    rcases e10 with h | h
    · exact h
    · exact absurd h hB
  rw [hA, zero_mul] at f10
  exact one_ne_zero f10

theorem not_odd_orderOf_swap [Finite K] (A B : GL (Fin 2) K) (τ : K ≃+* K) :
    ¬ Odd (orderOf (lr A B * frM τ * trM)) := by
  rintro ⟨k, hk⟩
  set x := lr A B * frM τ * trM with hx
  have htt : (trM : MulAut (VM K)) * trM = 1 := trM_mul_self
  have hx2 : IsNS (x ^ 2) := by
    refine ⟨A * GeneralLinearGroup.map τ.toRingHom B, B * GeneralLinearGroup.map τ.toRingHom A,
      τ * τ, ?_⟩
    rw [pow_two, hx, ← lr_mul, ← frM_mul]
    calc lr A B * frM τ * trM * (lr A B * frM τ * trM)
        = lr A B * frM τ * (trM * lr A B) * frM τ * trM := by group
      _ = lr A B * frM τ * lr B A * (trM * frM τ) * trM := by rw [trM_lr]; group
      _ = lr A B * (frM τ * lr B A) * frM τ * (trM * trM) := by rw [trM_frM]; group
      _ = _ := by
        rw [htt, frM_lr, mul_one]
        group
  have hpow : x ^ orderOf x = 1 := pow_orderOf_eq_one x
  rw [hk, pow_succ, pow_mul] at hpow
  have hy : IsNS ((x ^ 2) ^ k * (lr A B * frM τ)) := (hx2.pow k).mul ⟨A, B, τ, rfl⟩
  have h1 : (x ^ 2) ^ k * (lr A B * frM τ) * trM = 1 := by
    rw [mul_assoc, ← hx]
    exact hpow
  apply not_isNS_trM (K := K)
  have : (trM : MulAut (VM K)) = ((x ^ 2) ^ k * (lr A B * frM τ))⁻¹ :=
    (eq_inv_of_mul_eq_one_right h1)
  rw [this]
  exact hy.inv

@[expose] def IsUT (A : GL (Fin 2) K) : Prop := (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0

theorem isUT_one : IsUT (1 : GL (Fin 2) K) := by
  simp [IsUT]

theorem IsUT.mul {A B : GL (Fin 2) K} (hA : IsUT A) (hB : IsUT B) : IsUT (A * B) := by
  unfold IsUT at hA hB ⊢
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hA, hB, zero_mul, mul_zero, add_zero]

theorem IsUT.map {A : GL (Fin 2) K} (hA : IsUT A) (τ : K ≃+* K) :
    IsUT (GeneralLinearGroup.map τ.toRingHom A) := by
  unfold IsUT at hA ⊢
  change τ ((A : Matrix (Fin 2) (Fin 2) K) 1 0) = 0
  rw [hA, map_zero]

theorem IsUT.pow {A : GL (Fin 2) K} (hA : IsUT A) (k : ℕ) : IsUT (A ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact isUT_one
  | succ k ih => rw [pow_succ]; exact ih.mul hA

theorem IsUT.pow_apply_zero_zero {A : GL (Fin 2) K} (hA : IsUT A) (k : ℕ) :
    ((A ^ k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 =
      ((A : Matrix (Fin 2) (Fin 2) K) 0 0) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, ih, hA, mul_zero,
      add_zero, pow_succ]

theorem IsUT.pow_apply_one_one {A : GL (Fin 2) K} (hA : IsUT A) (k : ℕ) :
    ((A ^ k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 =
      ((A : Matrix (Fin 2) (Fin 2) K) 1 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := hA.pow k
    unfold IsUT at h
    rw [pow_succ, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, ih, h, zero_mul,
      zero_add, pow_succ]

theorem IsUT.apply_ne_zero {A : GL (Fin 2) K} (hA : IsUT A) :
    (A : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 ∧ (A : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
  have hdet : (A : Matrix (Fin 2) (Fin 2) K).det ≠ 0 :=
    (Matrix.isUnit_iff_isUnit_det _).mp A.isUnit |>.ne_zero
  unfold IsUT at hA
  rw [Matrix.det_fin_two, hA, mul_zero, sub_zero] at hdet
  exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩

theorem IsUT.sq_eq_one [CharP K 2] {A : GL (Fin 2) K} (hA : IsUT A)
    (h0 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 = 1) (h1 : (A : Matrix (Fin 2) (Fin 2) K) 1 1 = 1) :
    A ^ 2 = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  unfold IsUT at hA
  ext i j
  rw [pow_two, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [h0, h1, hA]
  linear_combination (A : Matrix (Fin 2) (Fin 2) K) 0 1 * h2

theorem IsUT.pow_card_sub_one_sq [Fintype K] [CharP K 2] {A : GL (Fin 2) K} (hA : IsUT A) :
    (A ^ (Fintype.card K - 1)) ^ 2 = 1 := by
  obtain ⟨h0, h1⟩ := hA.apply_ne_zero
  refine (hA.pow _).sq_eq_one ?_ ?_
  · rw [hA.pow_apply_zero_zero, FiniteField.pow_card_sub_one_eq_one _ h0]
  · rw [hA.pow_apply_one_one, FiniteField.pow_card_sub_one_eq_one _ h1]

theorem lr_pow (A B : GL (Fin 2) K) (k : ℕ) : lr A B ^ k = lr (A ^ k) (B ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, pow_zero, lr_one]
  | succ k ih => rw [pow_succ, ih, lr_mul, ← pow_succ, ← pow_succ]

theorem exists_pow_eq_of_isUT {A B : GL (Fin 2) K} (hA : IsUT A) (hB : IsUT B) (τ : K ≃+* K)
    (k : ℕ) : ∃ A' B' : GL (Fin 2) K, IsUT A' ∧ IsUT B' ∧
      (lr A B * frM τ) ^ k = lr A' B' * frM (τ ^ k) := by
  induction k with
  | zero => exact ⟨1, 1, isUT_one, isUT_one, by rw [pow_zero, pow_zero, lr_one, frM_one, mul_one]⟩
  | succ k ih =>
    obtain ⟨A', B', hA', hB', h⟩ := ih
    refine ⟨A' * GeneralLinearGroup.map (τ ^ k).toRingHom A,
      B' * GeneralLinearGroup.map (τ ^ k).toRingHom B, hA'.mul (hA.map _), hB'.mul (hB.map _), ?_⟩
    rw [pow_succ, h, pow_succ, ← frM_mul, ← lr_mul]
    calc lr A' B' * frM (τ ^ k) * (lr A B * frM τ)
        = lr A' B' * (frM (τ ^ k) * lr A B) * frM τ := by group
      _ = _ := by rw [frM_lr]; group

theorem pow_eq_one_of_isUT [Fintype K] [CharP K 2] {A B : GL (Fin 2) K} (hA : IsUT A)
    (hB : IsUT B) {τ : K ≃+* K} {k : ℕ} (hτ : τ ^ k = 1) :
    (lr A B * frM τ) ^ (k * (Fintype.card K - 1) * 2) = 1 := by
  obtain ⟨A', B', hA', hB', h⟩ := exists_pow_eq_of_isUT hA hB τ k
  rw [pow_mul, pow_mul, h, hτ, frM_one, mul_one, lr_pow, lr_pow, hA'.pow_card_sub_one_sq,
    hB'.pow_card_sub_one_sq, lr_one]

theorem toAdd_apply_smul_e11 (A B : GL (Fin 2) K) (τ : K ≃+* K) (c : K) :
    Multiplicative.toAdd ((lr A B * frM τ) (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0]))) =
      τ c • ((A : Matrix (Fin 2) (Fin 2) K) * !![(1 : K), 0; 0, 0] *
        (B : Matrix (Fin 2) (Fin 2) K)ᵀ) := by
  rw [MulAut.mul_apply, toAdd_lr, toAdd_frM, toAdd_ofAdd]
  have : (c • !![(1 : K), 0; 0, 0]).map τ = τ c • !![(1 : K), 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem trM_smul_e11 (c : K) :
    (trM : MulAut (VM K)) (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0])) =
      Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0]) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_trM, toAdd_ofAdd]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem isUT_of_mul_e11 {A B : GL (Fin 2) K} {μ : K}
    (h : (A : Matrix (Fin 2) (Fin 2) K) * !![(1 : K), 0; 0, 0] * (B : Matrix (Fin 2) (Fin 2) K)ᵀ =
      μ • !![(1 : K), 0; 0, 0]) : IsUT A ∧ IsUT B := by
  have e10 := congrFun (congrFun h 1) 0
  have e01 := congrFun (congrFun h 0) 1
  have e11 := congrFun (congrFun h 1) 1
  rw [mul_mul_transpose_entry] at e10 e01 e11
  simp at e10 e01 e11
  have hdA : (A : Matrix (Fin 2) (Fin 2) K).det ≠ 0 :=
    (Matrix.isUnit_iff_isUnit_det _).mp A.isUnit |>.ne_zero
  have hdB : (B : Matrix (Fin 2) (Fin 2) K).det ≠ 0 :=
    (Matrix.isUnit_iff_isUnit_det _).mp B.isUnit |>.ne_zero
  rw [Matrix.det_fin_two] at hdA hdB
  by_cases hA : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · refine ⟨hA, ?_⟩
    have hA0 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := fun h0 => hdA (by rw [h0, hA]; ring)
    rcases e01 with h1 | h1
    · exact absurd h1 hA0
    · exact h1
  · exfalso
    have hB0 : (B : Matrix (Fin 2) (Fin 2) K) 0 0 = 0 := e10.resolve_left hA
    have hB1 : (B : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := e11.resolve_left hA
    exact hdB (by rw [hB0, hB1]; ring)

theorem apply_smul_e11 {A B : GL (Fin 2) K} (hA : IsUT A) (hB : IsUT B) (τ : K ≃+* K) (c : K) :
    (lr A B * frM τ) (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0])) =
      Multiplicative.ofAdd (((A : Matrix (Fin 2) (Fin 2) K) 0 0 *
        (B : Matrix (Fin 2) (Fin 2) K) 0 0 * τ c) • !![(1 : K), 0; 0, 0]) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_apply_smul_e11, toAdd_ofAdd]
  unfold IsUT at hA hB
  ext i j
  rw [Matrix.smul_apply, mul_mul_transpose_entry]
  fin_cases i <;> fin_cases j <;> simp [hA, hB]
  ring

end CFSG.Quasithin.H.Om4
