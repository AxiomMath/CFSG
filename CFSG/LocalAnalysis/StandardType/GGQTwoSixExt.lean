module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSixDefs
public import CFSG.ClassicalInvolution.Phan.Phan3TAutA
public import CFSG.ClassicalInvolution.Phan.Coherent
public import CFSG.ClassicalInvolution.Phan.Parabolic

public section

namespace CFSG.StandardType.QTwo.SixPoint

open Matrix CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.LieType.BorelTits CFSG.LieType.Steinberg

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem qTwoSixExt_norm (hK : Nat.card K = 4) (a : Kˣ) :
    unitaryInvolution K 2 1 (a : K) * (a : K) = 1 := by
  let : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card_sub_one_eq_one (a : K) a.ne_zero
  rw [Fintype.card_eq_nat_card, hK] at h
  simpa only [unitaryInvolution_apply, pow_one, ← pow_succ] using h

noncomputable def qTwoSixExt_diagField (hK : Nat.card K = 4) {n : ℕ}
    (d : Fin n → Kˣ) (σ : K ≃+* K) : Su K 2 1 n ≃* Su K 2 1 n :=
  (fieldAutSU 2 1 σ n).trans
    (unitaryConj 2 1 (by simpa using hK) (diagGL d)
      (diagGL_conjTr_mul_self d fun i => qTwoSixExt_norm hK (d i)))

theorem qTwoSixExt_diagField_matrix (hK : Nat.card K = 4) {n : ℕ}
    (d : Fin n → Kˣ) (σ : K ≃+* K) (u : Su K 2 1 n) :
    (((qTwoSixExt_diagField hK d σ u : Su K 2 1 n) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) =
      diagonal (fun i => (d i : K)) *
        (((u : Su K 2 1 n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ *
        diagonal (fun i => (((d i)⁻¹ : Kˣ) : K)) := by
  simp only [qTwoSixExt_diagField, MulEquiv.trans_apply, coe_unitaryConj,
    Units.val_mul, coe_diagGL, coe_diagGL_inv, coe_coe_fieldAutSU]

theorem qTwoSixExt_diagField_mem (hK : Nat.card K = 4) {n : ℕ}
    (d : Fin n → Kˣ) (σ : K ≃+* K) (J : Finset (Fin n)) (u : Su K 2 1 n) :
    qTwoSixExt_diagField hK d σ u ∈ coordBlockSU K 2 1 J ↔
      u ∈ coordBlockSU K 2 1 J := by
  have hentry (i j : Fin n) :
      (((qTwoSixExt_diagField hK d σ u : Su K 2 1 n) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) i j =
      (d i : K) * σ ((((u : Su K 2 1 n) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) i j) * (((d j)⁻¹ : Kˣ) : K) := by
    rw [qTwoSixExt_diagField_matrix]
    simp only [diagonal_mul, mul_diagonal, map_apply]
  have hdelta (i j : Fin n) :
      (d i : K) * σ (if i = j then 1 else 0) * (((d j)⁻¹ : Kˣ) : K) =
        if i = j then 1 else 0 := by
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [mem_coordBlockSU_iff, mem_coordBlockSU_iff]
  constructor
  · intro h i j hij
    have he := h i j hij
    rw [hentry] at he
    apply σ.injective
    exact mul_left_cancel₀ (d i).ne_zero
      (mul_right_cancel₀ ((d j)⁻¹).ne_zero (he.trans (hdelta i j).symm))
  · intro h i j hij
    rw [hentry, h i j hij]
    exact hdelta i j

theorem qTwoSixExt_diagField_blocks (hK : Nat.card K = 4) {n : ℕ}
    (d : Fin n → Kˣ) (σ : K ≃+* K) (J : Finset (Fin n)) :
    (coordBlockSU K 2 1 J).map (qTwoSixExt_diagField hK d σ).toMonoidHom =
      coordBlockSU K 2 1 J := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (qTwoSixExt_diagField_mem hK d σ J v).2 hv
  · intro hu
    refine ⟨(qTwoSixExt_diagField hK d σ).symm u, ?_,
      (qTwoSixExt_diagField hK d σ).apply_symm_apply u⟩
    apply (qTwoSixExt_diagField_mem hK d σ J _).1
    simpa using hu

private def qTwoSixExt_extend (d : Fin 3 → Kˣ) : Fin 4 → Kˣ := ![d 0, d 1, d 2, 1]

omit [Finite K] [CharP K 2] in
private theorem qTwoSixExt_extend_matrix (d : Fin 3 → Kˣ) :
    diagonal (fun i => (qTwoSixExt_extend d i : K)) =
      blockMat 4 0 (diagonal (fun i => (d i : K))) := by
  ext i j
  rw [blockMat_apply]
  fin_cases i <;> fin_cases j <;> simp [qTwoSixExt_extend, diagonal]

omit [Finite K] [CharP K 2] in
private theorem qTwoSixExt_extend_inv_matrix (d : Fin 3 → Kˣ) :
    diagonal (fun i => (((qTwoSixExt_extend d i)⁻¹ : Kˣ) : K)) =
      blockMat 4 0 (diagonal (fun i => (((d i)⁻¹ : Kˣ) : K))) := by
  ext i j
  rw [blockMat_apply]
  fin_cases i <;> fin_cases j <;> simp [qTwoSixExt_extend, diagonal]

theorem qTwoSix_ext (hK : Nat.card K = 4) (d : Fin 3 → Kˣ) (σ : K ≃+* K) :
    ∃ β : Su K 2 1 4 ≃* Su K 2 1 4,
      (∀ J : Finset (Fin 4), (coordBlockSU K 2 1 J).map β.toMonoidHom = coordBlockSU K 2 1 J) ∧
      ∀ u : Su K 2 1 3,
        (((β (blockEmb K 2 1 4 3 0 (by norm_num) u) : Su K 2 1 4) : GL (Fin 4) K) :
            Matrix (Fin 4) (Fin 4) K) =
          blockMat 4 0 (diagonal (fun i => (d i : K)) *
            (((u : Su K 2 1 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ *
            diagonal (fun i => (((d i)⁻¹ : Kˣ) : K))) := by
  refine ⟨qTwoSixExt_diagField hK (qTwoSixExt_extend d) σ,
    fun J => qTwoSixExt_diagField_blocks hK _ σ J, ?_⟩
  intro u
  rw [qTwoSixExt_diagField_matrix, coe_coe_blockEmb, Q3G.autA_map_blockMat,
    qTwoSixExt_extend_matrix, qTwoSixExt_extend_inv_matrix,
    ← blockMat_mul (by norm_num : 0 + 3 ≤ 4),
    ← blockMat_mul (by norm_num : 0 + 3 ≤ 4)]

end CFSG.StandardType.QTwo.SixPoint

end
