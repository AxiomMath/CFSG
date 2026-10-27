module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Rows

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open
open Matrix
open scoped commutatorElement

private theorem k328r7f_charP (F : Type) [Field F] [Fintype F]
    (hF : Fintype.card F = 8) : CharP F 2 :=
  ringChar.of_eq (FiniteField.even_card_iff_char_two.mpr (by rw [hF]))

private theorem k328r7f_rhoL_mul (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (A₀ A₁ B₀ B₁ : Matrix (Fin 3) (Fin 3) F) :
    rhoL F A₀ A₁ * rhoL F B₀ B₁ =
      rhoL F (A₀ * B₀ + A₁ * B₁) (A₀ * B₁ + A₁ * B₀ + A₁ * B₁) := by
  simp only [rhoL, Matrix.fromBlocks_multiply]
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring

private theorem k328r7f_rhoL_one (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    rhoL F 1 0 = (1 : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) := by
  simp [rhoL]

private theorem k328r7f_rhoL_eq_iff (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (A₀ A₁ B₀ B₁ : Matrix (Fin 3) (Fin 3) F) :
    rhoL F A₀ A₁ = rhoL F B₀ B₁ ↔ A₀ = B₀ ∧ A₁ = B₁ := by
  simp only [rhoL, Matrix.fromBlocks_inj]
  constructor
  · rintro ⟨h1, h2, _, _⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2, h2, by rw [h1, h2]⟩

private def k328r7f_matP (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

private def k328r7f_matPinv (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    Matrix (Fin 3) (Fin 3) F := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

private def k328r7f_matTau (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    Matrix (Fin 3) (Fin 3) F := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

private def k328r7f_matDz0 (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    Matrix (Fin 3) (Fin 3) F := Matrix.diagonal ![1, 1, 0]

private def k328r7f_matDz1 (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    Matrix (Fin 3) (Fin 3) F := Matrix.diagonal ![0, 1, 1]

private def k328r7f_matDt0 (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    Matrix (Fin 3) (Fin 3) F := Matrix.diagonal ![1, 0, 1]

private theorem k328r7f_matP_mul_Pinv (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    k328r7f_matP F * k328r7f_matPinv F = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [k328r7f_matP, k328r7f_matPinv, Matrix.mul_apply, Fin.sum_univ_three]

private theorem k328r7f_matPinv_mul_P (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    k328r7f_matPinv F * k328r7f_matP F = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [k328r7f_matP, k328r7f_matPinv, Matrix.mul_apply, Fin.sum_univ_three]

private theorem k328r7f_matTau_sq (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    k328r7f_matTau F * k328r7f_matTau F = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [k328r7f_matTau, Matrix.mul_apply, Fin.sum_univ_three]

private def k328r7f_Phat (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    GL (Fin 3 ⊕ Fin 3) F :=
  ⟨rhoL F (k328r7f_matP F) 0, rhoL F (k328r7f_matPinv F) 0,
    by rw [k328r7f_rhoL_mul, k328r7f_matP_mul_Pinv]; simp [k328r7f_rhoL_one],
    by rw [k328r7f_rhoL_mul, k328r7f_matPinv_mul_P]; simp [k328r7f_rhoL_one]⟩

private def k328r7f_tauHat (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    GL (Fin 3 ⊕ Fin 3) F :=
  ⟨rhoL F (k328r7f_matTau F) 0, rhoL F (k328r7f_matTau F) 0,
    by rw [k328r7f_rhoL_mul, k328r7f_matTau_sq]; simp [k328r7f_rhoL_one],
    by rw [k328r7f_rhoL_mul, k328r7f_matTau_sq]; simp [k328r7f_rhoL_one]⟩

private theorem k328r7f_Dz_mul_Dt (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] :
    rhoL F (k328r7f_matDz0 F) (k328r7f_matDz1 F) *
      rhoL F (k328r7f_matDt0 F) (k328r7f_matDz1 F) = 1 := by
  rw [k328r7f_rhoL_mul, ← k328r7f_rhoL_one, k328r7f_rhoL_eq_iff]
  refine ⟨?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [k328r7f_matDz0, k328r7f_matDz1, k328r7f_matDt0,
        CharTwo.add_self_eq_zero]

private theorem k328r7f_Dt_mul_Dz (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] :
    rhoL F (k328r7f_matDt0 F) (k328r7f_matDz1 F) *
      rhoL F (k328r7f_matDz0 F) (k328r7f_matDz1 F) = 1 := by
  rw [k328r7f_rhoL_mul, ← k328r7f_rhoL_one, k328r7f_rhoL_eq_iff]
  refine ⟨?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [k328r7f_matDz0, k328r7f_matDz1, k328r7f_matDt0,
        CharTwo.add_self_eq_zero]

private def k328r7f_Dz (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] :
    GL (Fin 3 ⊕ Fin 3) F :=
  ⟨rhoL F (k328r7f_matDz0 F) (k328r7f_matDz1 F),
    rhoL F (k328r7f_matDt0 F) (k328r7f_matDz1 F),
    k328r7f_Dz_mul_Dt F, k328r7f_Dt_mul_Dz F⟩

private def k328r7f_Dt (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] :
    GL (Fin 3 ⊕ Fin 3) F :=
  ⟨rhoL F (k328r7f_matDt0 F) (k328r7f_matDz1 F),
    rhoL F (k328r7f_matDz0 F) (k328r7f_matDz1 F),
    k328r7f_Dt_mul_Dz F, k328r7f_Dz_mul_Dt F⟩

private theorem k328r7f_Phat_mem_H (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] : k328r7f_Phat F ∈ StatedSp 3 F := by
  rw [StatedAPI.mem_statedSp_iff]
  change (rhoL F (k328r7f_matP F) 0)ᵀ * fromBlocks 0 1 (-1) 0 *
      rhoL F (k328r7f_matP F) 0 = fromBlocks 0 1 (-1) 0
  simp only [rhoL, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
    Matrix.fromBlocks_multiply]
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [k328r7f_matP, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
        CharTwo.neg_eq, CharTwo.add_self_eq_zero]

private theorem k328r7f_tauHat_mem_H (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] : k328r7f_tauHat F ∈ StatedSp 3 F := by
  rw [StatedAPI.mem_statedSp_iff]
  change (rhoL F (k328r7f_matTau F) 0)ᵀ * fromBlocks 0 1 (-1) 0 *
      rhoL F (k328r7f_matTau F) 0 = fromBlocks 0 1 (-1) 0
  simp only [rhoL, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
    Matrix.fromBlocks_multiply]
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [k328r7f_matTau, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
        CharTwo.neg_eq, CharTwo.add_self_eq_zero]

private theorem k328r7f_Dz_mem_H (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] : k328r7f_Dz F ∈ StatedSp 3 F := by
  rw [StatedAPI.mem_statedSp_iff]
  change (rhoL F (k328r7f_matDz0 F) (k328r7f_matDz1 F))ᵀ * fromBlocks 0 1 (-1) 0 *
      rhoL F (k328r7f_matDz0 F) (k328r7f_matDz1 F) = fromBlocks 0 1 (-1) 0
  simp only [rhoL, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [k328r7f_matDz0, k328r7f_matDz1,
        CharTwo.neg_eq,
        CharTwo.add_self_eq_zero]

private theorem k328r7f_Dt_mem_H (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] : k328r7f_Dt F ∈ StatedSp 3 F := by
  rw [StatedAPI.mem_statedSp_iff]
  change (rhoL F (k328r7f_matDt0 F) (k328r7f_matDz1 F))ᵀ * fromBlocks 0 1 (-1) 0 *
      rhoL F (k328r7f_matDt0 F) (k328r7f_matDz1 F) = fromBlocks 0 1 (-1) 0
  simp only [rhoL, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [k328r7f_matDt0, k328r7f_matDz1,
        CharTwo.neg_eq,
        CharTwo.add_self_eq_zero]

private theorem k328r7f_rhoL_comm_z0 (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (A₀ A₁ : Matrix (Fin 3) (Fin 3) F) :
    rhoL F A₀ A₁ * rhoL F 0 1 = rhoL F 0 1 * rhoL F A₀ A₁ := by
  rw [k328r7f_rhoL_mul, k328r7f_rhoL_mul, k328r7f_rhoL_eq_iff]
  refine ⟨?_, ?_⟩ <;> noncomm_ring

private theorem k328r7f_Phat_commutator_Dz (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] :
    ((⁅k328r7f_Phat F, k328r7f_Dz F⁆ : GL (Fin 3 ⊕ Fin 3) F) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = rhoL F 0 1 := by
  rw [commutatorElement_def]
  simp only [Units.val_mul]
  change rhoL F (k328r7f_matP F) 0 * rhoL F (k328r7f_matDz0 F) (k328r7f_matDz1 F) *
      rhoL F (k328r7f_matPinv F) 0 * rhoL F (k328r7f_matDt0 F) (k328r7f_matDz1 F) =
      rhoL F 0 1
  rw [k328r7f_rhoL_mul, k328r7f_rhoL_mul, k328r7f_rhoL_mul, k328r7f_rhoL_eq_iff]
  refine ⟨?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [k328r7f_matP, k328r7f_matPinv, k328r7f_matDz0, k328r7f_matDz1,
        k328r7f_matDt0, Matrix.mul_apply, Matrix.vecMul_apply,
        dotProduct, Fin.sum_univ_three, Matrix.diagonal_apply,
        CharTwo.add_self_eq_zero]

private theorem k328r7f_tauHat_commutator_Dt (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [CharP F 2] :
    ((⁅k328r7f_tauHat F, k328r7f_Dt F⁆ : GL (Fin 3 ⊕ Fin 3) F) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      rhoL F (k328r7f_matDz1 F) (k328r7f_matDz0 F) := by
  rw [commutatorElement_def]
  simp only [Units.val_mul]
  change rhoL F (k328r7f_matTau F) 0 * rhoL F (k328r7f_matDt0 F) (k328r7f_matDz1 F) *
      rhoL F (k328r7f_matTau F) 0 * rhoL F (k328r7f_matDz0 F) (k328r7f_matDz1 F) =
      rhoL F (k328r7f_matDz1 F) (k328r7f_matDz0 F)
  rw [k328r7f_rhoL_mul, k328r7f_rhoL_mul, k328r7f_rhoL_mul, k328r7f_rhoL_eq_iff]
  refine ⟨?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [k328r7f_matTau, k328r7f_matDz0, k328r7f_matDz1, k328r7f_matDt0,
        Matrix.mul_apply, Matrix.vecMul_apply,
        dotProduct, Fin.sum_univ_three, Matrix.diagonal_apply,
        CharTwo.add_self_eq_zero]

theorem row7_facts (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 8) (z₀ t₀ : GL (Fin 3 ⊕ Fin 3) F)
    (hz : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = rhoL F 0 1)
    (ht : (t₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      rhoL F (Matrix.diagonal ![0, 1, 1]) (Matrix.diagonal ![1, 1, 0])) :
    FactsLeaf (StatedSp 3 F) z₀ t₀ := by
  have : CharP F 2 := k328r7f_charP F hF
  have hz0_mem : z₀ ∈ StatedSp 3 F := by
    rw [StatedAPI.mem_statedSp_iff, hz]
    simp only [rhoL, Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_one,
      Matrix.fromBlocks_multiply]
    rw [Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      ext i j <;> fin_cases i <;> fin_cases j <;>
        simp [CharTwo.neg_eq, CharTwo.add_self_eq_zero]
  have ht0_mem : t₀ ∈ StatedSp 3 F := by
    rw [StatedAPI.mem_statedSp_iff, ht]
    simp only [rhoL, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
    rw [Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      ext i j <;> fin_cases i <;> fin_cases j <;>
        simp [
          CharTwo.neg_eq, CharTwo.add_self_eq_zero]
  have hz0_order : orderOf z₀ = 3 := by
    apply orderOf_eq_prime
    · apply Units.ext
      rw [Units.val_pow_eq_pow_val, hz]
      have h2 : rhoL F 0 1 * rhoL F 0 1 = rhoL F 1 1 := by
        simp [k328r7f_rhoL_mul]
      have h3 : rhoL F 1 1 * rhoL F 0 1 = rhoL F 1 0 := by
        simp [k328r7f_rhoL_mul, CharTwo.add_self_eq_zero]
      change (rhoL F 0 1) ^ (2 + 1) = 1
      rw [pow_succ, pow_two, h2, h3, k328r7f_rhoL_one]
    · intro h
      have h' : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = 1 := Units.ext_iff.mp h
      rw [hz] at h'
      simp only [rhoL] at h'
      rw [← Matrix.fromBlocks_one] at h'
      rw [Matrix.fromBlocks_inj] at h'
      obtain ⟨h10, _, _, _⟩ := h'
      have : (0 : Matrix (Fin 3) (Fin 3) F) ≠ 1 := by
        intro hc
        have := congrFun (congrFun hc 0) 0
        simp at this
      exact this h10
  have ht0_order : orderOf t₀ = 3 := by
    set A0 : Matrix (Fin 3) (Fin 3) F := Matrix.diagonal ![0, 1, 1] with hA0
    set A1 : Matrix (Fin 3) (Fin 3) F := Matrix.diagonal ![1, 1, 0] with hA1
    apply orderOf_eq_prime
    · apply Units.ext
      rw [Units.val_pow_eq_pow_val, ht]
      have hA0sq : A0 * A0 = A0 := by
        rw [hA0]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Matrix.diagonal_apply]
      have hA1sq : A1 * A1 = A1 := by
        rw [hA1]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Matrix.diagonal_apply]
      have hA0A1 : A0 * A1 = Matrix.diagonal ![0, 1, 0] := by
        rw [hA0, hA1]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Matrix.diagonal_apply]
      have hA1A0 : A1 * A0 = Matrix.diagonal ![0, 1, 0] := by
        rw [hA0, hA1]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Matrix.diagonal_apply]
      have h2 : rhoL F A0 A1 * rhoL F A0 A1 =
          rhoL F (Matrix.diagonal ![1, 0, 1]) (Matrix.diagonal ![1, 1, 0]) := by
        rw [k328r7f_rhoL_mul, k328r7f_rhoL_eq_iff]
        refine ⟨?_, ?_⟩
        · rw [hA0sq, hA1sq, hA0, hA1]
          ext i j; fin_cases i <;> fin_cases j <;>
            simp [CharTwo.add_self_eq_zero]
        · rw [hA0A1, hA1A0, hA1sq, hA1]
          ext i j; fin_cases i <;> fin_cases j <;>
            simp [CharTwo.add_self_eq_zero]
      have h3 : rhoL F (Matrix.diagonal ![1, 0, 1]) (Matrix.diagonal ![1, 1, 0]) *
          rhoL F A0 A1 = rhoL F 1 0 := by
        rw [k328r7f_rhoL_mul, k328r7f_rhoL_eq_iff]
        refine ⟨?_, ?_⟩
        · rw [hA0, hA1]
          ext i j; fin_cases i <;> fin_cases j <;>
            simp [
              CharTwo.add_self_eq_zero]
        · rw [hA0, hA1]
          ext i j; fin_cases i <;> fin_cases j <;>
            simp [
              CharTwo.add_self_eq_zero]
      change (rhoL F A0 A1) ^ (2 + 1) = 1
      rw [pow_succ, pow_two, h2, h3, k328r7f_rhoL_one]
    · intro h
      have h' : (t₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = 1 := Units.ext_iff.mp h
      rw [ht] at h'
      simp only [rhoL] at h'
      rw [← Matrix.fromBlocks_one] at h'
      rw [Matrix.fromBlocks_inj] at h'
      obtain ⟨_, h11, _, _⟩ := h'
      have : (Matrix.diagonal ![1, 1, 0] : Matrix (Fin 3) (Fin 3) F) ≠ 0 := by
        intro hc
        have := congrFun (congrFun hc 0) 0
        simp at this
      exact this h11
  have hcomm : z₀ * t₀ = t₀ * z₀ := by
    apply Units.ext
    simp only [Units.val_mul, hz, ht]
    rw [k328r7f_rhoL_mul, k328r7f_rhoL_mul, k328r7f_rhoL_eq_iff]
    refine ⟨?_, ?_⟩ <;>
      ext i j <;> fin_cases i <;> fin_cases j <;>
        simp []
  have hnot : t₀ ∉ Subgroup.zpowers z₀ := by
    intro h
    rw [Subgroup.mem_zpowers_iff] at h
    obtain ⟨k, hk⟩ := h
    have hmod : z₀ ^ (k % (3 : ℤ)) = t₀ := by
      rw [← hk]
      have h_ord : (3 : ℤ) = (orderOf z₀ : ℤ) := by rw [hz0_order]; norm_num
      rw [h_ord, zpow_mod_orderOf]
    have hkmod_nonneg : 0 ≤ k % (3 : ℤ) := Int.emod_nonneg k (by norm_num)
    have hkmod_lt : k % (3 : ℤ) < 3 := Int.emod_lt_of_pos k (by norm_num)
    interval_cases hkmod : k % (3 : ℤ)
    · simp at hmod
      have ht1 : t₀ ≠ 1 := by
        intro h1
        have h1' : (t₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = 1 := Units.ext_iff.mp h1
        rw [ht] at h1'
        simp only [rhoL] at h1'
        rw [← Matrix.fromBlocks_one] at h1'
        rw [Matrix.fromBlocks_inj] at h1'
        obtain ⟨_, h11, _, _⟩ := h1'
        have : (Matrix.diagonal ![1, 1, 0] : Matrix (Fin 3) (Fin 3) F) ≠ 0 := by
          intro hc
          have := congrFun (congrFun hc 0) 0
          simp at this
        exact this h11
      exact ht1 hmod.symm
    · simp [] at hmod
      have htz : t₀ ≠ z₀ := by
        intro h1
        have h1' : (t₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
            (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) := Units.ext_iff.mp h1
        rw [ht, hz] at h1'
        rw [k328r7f_rhoL_eq_iff] at h1'
        obtain ⟨h10, _⟩ := h1'
        have : (Matrix.diagonal ![0, 1, 1] : Matrix (Fin 3) (Fin 3) F) ≠ 0 := by
          intro hc
          have := congrFun (congrFun hc 1) 1
          simp at this
        exact this h10
      exact htz hmod.symm
    · have hzsq : z₀ ^ (2 : ℤ) = z₀ * z₀ := by simp [sq]
      rw [hzsq] at hmod
      have hmod' : ((z₀ * z₀ : GL (Fin 3 ⊕ Fin 3) F) :
          Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
          (t₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) := Units.ext_iff.mp hmod
      rw [Units.val_mul, hz] at hmod'
      have h2 : rhoL F 0 1 * rhoL F 0 1 = rhoL F 1 1 := by
        simp [k328r7f_rhoL_mul]
      rw [h2, ht] at hmod'
      rw [k328r7f_rhoL_eq_iff] at hmod'
      obtain ⟨h10, _⟩ := hmod'
      have : (Matrix.diagonal ![0, 1, 1] : Matrix (Fin 3) (Fin 3) F) ≠ 1 := by
        intro hc
        have := congrFun (congrFun hc 0) 0
        simp at this
      exact this h10.symm
  have hPhatC : k328r7f_Phat F ∈ StatedSp 3 F ⊓ Subgroup.centralizer {z₀} := by
    refine ⟨k328r7f_Phat_mem_H F, ?_⟩
    change k328r7f_Phat F ∈ Subgroup.centralizer {z₀}
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    apply Units.ext
    change (z₀ : Matrix _ _ F) * rhoL F (k328r7f_matP F) 0 =
      rhoL F (k328r7f_matP F) 0 * (z₀ : Matrix _ _ F)
    rw [hz]
    exact (k328r7f_rhoL_comm_z0 F (k328r7f_matP F) 0).symm
  have hDzC : k328r7f_Dz F ∈ StatedSp 3 F ⊓ Subgroup.centralizer {z₀} := by
    refine ⟨k328r7f_Dz_mem_H F, ?_⟩
    change k328r7f_Dz F ∈ Subgroup.centralizer {z₀}
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    apply Units.ext
    change (z₀ : Matrix _ _ F) * rhoL F (k328r7f_matDz0 F) (k328r7f_matDz1 F) =
      rhoL F (k328r7f_matDz0 F) (k328r7f_matDz1 F) * (z₀ : Matrix _ _ F)
    rw [hz]
    exact (k328r7f_rhoL_comm_z0 F (k328r7f_matDz0 F) (k328r7f_matDz1 F)).symm
  have htauHatC : k328r7f_tauHat F ∈ StatedSp 3 F ⊓ Subgroup.centralizer {z₀} := by
    refine ⟨k328r7f_tauHat_mem_H F, ?_⟩
    change k328r7f_tauHat F ∈ Subgroup.centralizer {z₀}
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    apply Units.ext
    change (z₀ : Matrix _ _ F) * rhoL F (k328r7f_matTau F) 0 =
      rhoL F (k328r7f_matTau F) 0 * (z₀ : Matrix _ _ F)
    rw [hz]
    exact (k328r7f_rhoL_comm_z0 F (k328r7f_matTau F) 0).symm
  have hDtC : k328r7f_Dt F ∈ StatedSp 3 F ⊓ Subgroup.centralizer {z₀} := by
    refine ⟨k328r7f_Dt_mem_H F, ?_⟩
    change k328r7f_Dt F ∈ Subgroup.centralizer {z₀}
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    apply Units.ext
    change (z₀ : Matrix _ _ F) * rhoL F (k328r7f_matDt0 F) (k328r7f_matDz1 F) =
      rhoL F (k328r7f_matDt0 F) (k328r7f_matDz1 F) * (z₀ : Matrix _ _ F)
    rw [hz]
    exact (k328r7f_rhoL_comm_z0 F (k328r7f_matDt0 F) (k328r7f_matDz1 F)).symm
  have hz0_stdComp : z₀ ∈ stdComp (StatedSp 3 F) z₀ := by
    have hmem := Subgroup.commutator_mem_commutator hPhatC hDzC
    have heq : (⁅k328r7f_Phat F, k328r7f_Dz F⁆ : GL (Fin 3 ⊕ Fin 3) F) = z₀ := by
      apply Units.ext
      simpa [hz] using k328r7f_Phat_commutator_Dz F
    rw [heq] at hmem
    exact hmem
  have ht0_stdComp : t₀ ∈ stdComp (StatedSp 3 F) z₀ := by
    have hmem := Subgroup.commutator_mem_commutator htauHatC hDtC
    have heq : (⁅k328r7f_tauHat F, k328r7f_Dt F⁆ : GL (Fin 3 ⊕ Fin 3) F) = t₀ := by
      apply Units.ext
      rw [k328r7f_tauHat_commutator_Dt F, ht]
      simp [k328r7f_matDz0, k328r7f_matDz1]
    rw [heq] at hmem
    exact hmem
  exact ⟨hz0_mem, hz0_stdComp, ht0_stdComp, hz0_order, ht0_order, hcomm, hnot⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
