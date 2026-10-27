module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SLModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Open
open CFSG.ClassicalInvolution.Phan
open Matrix

variable {k : ℕ} {K : Type} [Field K]

theorem exists_sqrt_inv_of_orderOf_odd {c : K} {r : ℕ} (hr : Odd r) (hc : orderOf c = r) :
    ∃ b : K, b ^ 2 = c⁻¹ ∧ orderOf b = r := by
  obtain ⟨m, rfl⟩ := hr
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [orderOf_zero] at hc
    omega
  let u : Kˣ := Units.mk0 c hc0
  have huo : orderOf u = 2 * m + 1 := by
    rw [← hc, ← orderOf_units]
    rfl
  have hu1 : u⁻¹ ^ (2 * m + 1) = 1 := by
    rw [inv_pow, ← huo, pow_orderOf_eq_one, inv_one]
  refine ⟨((u⁻¹ ^ (m + 1) : Kˣ) : K), ?_, ?_⟩
  · rw [← Units.val_pow_eq_pow_val, ← pow_mul]
    have h2 : (m + 1) * 2 = (2 * m + 1) + 1 := by ring
    rw [h2, pow_succ, hu1, one_mul]
    simp [u]
  · have hcop : (orderOf u⁻¹).Coprime (m + 1) := by
      rw [orderOf_inv, huo]
      have h : 2 * m + 1 = m + (m + 1) := by ring
      rw [h]
      simp
    rw [orderOf_units, hcop.orderOf_pow, orderOf_inv, huo]

theorem exists_sl2_diagonal {b : K} (hb : b ≠ 0) :
    ∃ D : Matrix.SpecialLinearGroup (Fin 2) K,
      (D : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![b, b⁻¹] :=
  ⟨⟨Matrix.diagonal ![b, b⁻¹], by
      rw [Matrix.det_diagonal, Fin.prod_univ_two]
      simp [hb]⟩, rfl⟩

theorem orderOf_slRootEmb_diagonal (hk : 3 ≤ k) {b : K} (hb : b ≠ 0)
    {D : Matrix.SpecialLinearGroup (Fin 2) K}
    (hD : (D : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![b, b⁻¹]) :
    orderOf (slRootEmb k hk K D) = orderOf b := by
  rw [orderOf_injective (slRootEmb k hk K) (slRootEmb_injective hk) D, orderOf_eq_orderOf_iff]
  intro n
  have hpow : ((D ^ n : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal (![b, b⁻¹] ^ n) := by
    rw [Matrix.SpecialLinearGroup.coe_pow, hD, Matrix.diagonal_pow]
  constructor
  · intro h1
    have h00 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) K =>
      (M : Matrix (Fin 2) (Fin 2) K) 0 0) h1
    simpa [hpow] using h00
  · intro h1
    apply Subtype.ext
    rw [hpow, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply, h1, inv_pow]

private lemma intertwine_left_B05 (hk : 3 ≤ k) {c : K} {t' : ↥(StatedSL k K)}
    (h : slMat t' = Matrix.diagonal (slTorusDiag k c)) :
    slMat t' * blockSel K k 2 1 = blockSel K k 2 1 * Matrix.diagonal ![c⁻¹, 1] := by
  rw [h]
  ext a j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [blockSel_apply]
  fin_cases j
  · by_cases ha : (a : ℕ) = 1
    · simp [slTorusDiag, ha]
    · simp [ha]
  · by_cases ha : (a : ℕ) = 2
    · simp [slTorusDiag, ha]
    · simp [ha]

private lemma intertwine_right_B05 (hk : 3 ≤ k) {c : K} {t' : ↥(StatedSL k K)}
    (h : slMat t' = Matrix.diagonal (slTorusDiag k c)) :
    (blockSel K k 2 1)ᵀ * slMat t' = Matrix.diagonal ![c⁻¹, 1] * (blockSel K k 2 1)ᵀ := by
  rw [h]
  ext j a
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.transpose_apply, blockSel_apply]
  fin_cases j
  · by_cases ha : (a : ℕ) = 1
    · simp [slTorusDiag, ha]
    · simp [ha]
  · by_cases ha : (a : ℕ) = 2
    · simp [slTorusDiag, ha]
    · simp [ha]

private lemma diag_conj_B05 {c b : K} (hc : c ≠ 0) (hbc : b ^ 2 = c⁻¹)
    {D : Matrix.SpecialLinearGroup (Fin 2) K}
    (hD : (D : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![b, b⁻¹])
    (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    (Matrix.diagonal ![c⁻¹, 1] : Matrix (Fin 2) (Fin 2) K) *
        (A : Matrix (Fin 2) (Fin 2) K) * Matrix.diagonal ![c, 1] =
      ((D * A * D⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hbc
    exact hc (inv_eq_zero.mp hbc.symm)
  obtain rfl : c = (b ^ 2)⁻¹ := by rw [hbc, inv_inv]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, hD, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem conj_slRootEmb_of_slMat_eq_diagonal (hk : 3 ≤ k) {c b : K} (hc : c ≠ 0) (hbc : b ^ 2 = c⁻¹)
    {t' : ↥(StatedSL k K)} (h : slMat t' = Matrix.diagonal (slTorusDiag k c))
    {D : Matrix.SpecialLinearGroup (Fin 2) K}
    (hD : (D : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![b, b⁻¹])
    (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    t' * slRootEmb k hk K A * t'⁻¹ = slRootEmb k hk K (D * A * D⁻¹) := by
  have hMM' : (Matrix.diagonal ![c⁻¹, 1] : Matrix (Fin 2) (Fin 2) K) *
      Matrix.diagonal ![c, 1] = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hc]
  have hmul : ∀ x y z : ↥(StatedSL k K),
      slMat (x * y * z) = slMat x * slMat y * slMat z := by
    intro x y z
    simp [slMat, Subgroup.coe_mul, Units.val_mul]
  have hWW' : slMat t' * slMat t'⁻¹ = 1 := by
    have h1 := hmul t' t'⁻¹ 1
    rw [mul_inv_cancel, one_mul] at h1
    rw [show slMat (1 : ↥(StatedSL k K)) = 1 by rfl, mul_one] at h1
    exact h1.symm
  have key := conj_blockMat_of_intertwine (F := K) hWW' hMM'
    (intertwine_left_B05 hk h) (intertwine_right_B05 hk h) (A : Matrix (Fin 2) (Fin 2) K)
  apply Subtype.ext
  apply Units.ext
  show slMat (t' * slRootEmb k hk K A * t'⁻¹) = slMat (slRootEmb k hk K (D * A * D⁻¹))
  rw [hmul]
  show slMat t' * blockMat k 1 (A : Matrix (Fin 2) (Fin 2) K) * slMat t'⁻¹ =
    blockMat k 1 (↑(D * A * D⁻¹) : Matrix (Fin 2) (Fin 2) K)
  rw [key, diag_conj_B05 hc hbc hD A]

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
