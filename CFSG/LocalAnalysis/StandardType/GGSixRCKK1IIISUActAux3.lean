module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISUActAux2

public section

namespace CFSG.StandardType.RCKK1IIISU

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {k : ℕ}

theorem rckSUc_g_mul_A_tau (hk : 4 ≤ k) (B : GL (Fin k) SUF) (τ : SUF ≃+* SUF)
    (hB : conjTr SUσ (B : Matrix (Fin k) (Fin k) SUF) * rckSUc_J k *
      (B : Matrix (Fin k) (Fin k) SUF) = rckSUc_J k)
    (hBN : (B : Matrix (Fin k) (Fin k) SUF) * rckSUc_N hk = rckSUc_N hk *
      (B : Matrix (Fin k) (Fin k) SUF)) (v : Fin 4 → ZMod 2) :
    rckSUc_g hk (B : Matrix (Fin k) (Fin k) SUF) * (rckSUc_A v).map τ
      = rckSUc_A ((rckSUc_psi hk B τ hB hBN : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v)
        * rckSUc_h hk (B : Matrix (Fin k) (Fin k) SUF) := by
  rw [rckSUc_A_psi hk B τ hB hBN v]
  simp only [Matrix.mul_assoc]
  rw [rckSUc_gstar_mul_h hk (B : Matrix (Fin k) (Fin k) SUF) hB hBN, Matrix.mul_one]

theorem rckSUc_map_one_k (hk : 4 ≤ k) (τ : SUF ≃+* SUF) :
    (1 : Matrix (Fin k) (Fin k) SUF).map τ = 1 := by
  ext i j
  simp [Matrix.map_apply, Matrix.one_apply]

theorem rckSUc_B_mul_M_rev0 (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (τ : SUF ≃+* SUF) (v : Fin 4 → ZMod 2) (i : Fin k) :
    (B * (rckSUc_M hk v).map τ) i (rckSUc_e' hk 0)
      = B i (rckSUc_e hk 0) * τ (rckSUc_alpha (v 0))
        + B i (rckSUc_e hk 1) * τ (SUσ (rckSUc_beta v)) := by
  rw [rckSUc_M_map, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add]
  simp only [Matrix.add_apply, rckSUc_mul_single_apply]
  simp [rckSUc_e'_zero_ne_one hk, rckSUc_e'_one_ne_zero hk]

theorem rckSUc_B_mul_M_rev1 (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (τ : SUF ≃+* SUF) (v : Fin 4 → ZMod 2) (i : Fin k) :
    (B * (rckSUc_M hk v).map τ) i (rckSUc_e' hk 1)
      = B i (rckSUc_e hk 0) * τ (rckSUc_beta v)
        + B i (rckSUc_e hk 1) * τ (rckSUc_alpha (v 3)) := by
  rw [rckSUc_M_map, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add]
  simp only [Matrix.add_apply, rckSUc_mul_single_apply]
  simp [rckSUc_e'_zero_ne_one hk, rckSUc_e'_one_ne_zero hk]

theorem rckSUc_B_mul_M_off (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (τ : SUF ≃+* SUF) (v : Fin 4 → ZMod 2) (i j : Fin k)
    (hj0 : j ≠ rckSUc_e' hk 0) (hj1 : j ≠ rckSUc_e' hk 1) :
    (B * (rckSUc_M hk v).map τ) i j = 0 := by
  rw [rckSUc_M_map, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add]
  simp only [Matrix.add_apply, rckSUc_mul_single_apply]
  simp [hj0, hj1]

theorem rckSUc_B_mul_M_zero_left (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (hBN : B * rckSUc_N hk = rckSUc_N hk * B) (τ : SUF ≃+* SUF) (v : Fin 4 → ZMod 2)
    (i : Fin k) (hi0 : i ≠ rckSUc_e hk 0) (hi1 : i ≠ rckSUc_e hk 1) (j : Fin k) :
    (B * (rckSUc_M hk v).map τ) i j = 0 := by
  rw [rckSUc_M_map, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add]
  simp only [Matrix.add_apply, rckSUc_mul_single_apply]
  simp [(rckSUc_B_col_of_ne hk B hBN i hi0 hi1).1,
    (rckSUc_B_col_of_ne hk B hBN i hi0 hi1).2]

theorem rckSUc_M_mul_B_row0 (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (v : Fin 4 → ZMod 2) (j : Fin k) :
    (rckSUc_M hk v * B) (rckSUc_e hk 0) j
      = rckSUc_alpha (v 0) * B (rckSUc_e' hk 0) j
        + rckSUc_beta v * B (rckSUc_e' hk 1) j := by
  rw [rckSUc_M, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul]
  simp only [Matrix.add_apply, rckSUc_single_mul_apply]
  simp [rckSUc_e_zero_ne_one hk]

theorem rckSUc_M_mul_B_row1 (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (v : Fin 4 → ZMod 2) (j : Fin k) :
    (rckSUc_M hk v * B) (rckSUc_e hk 1) j
      = SUσ (rckSUc_beta v) * B (rckSUc_e' hk 0) j
        + rckSUc_alpha (v 3) * B (rckSUc_e' hk 1) j := by
  rw [rckSUc_M, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul]
  simp only [Matrix.add_apply, rckSUc_single_mul_apply]
  simp [rckSUc_e_one_ne_zero hk]

theorem rckSUc_M_mul_B_off (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (v : Fin 4 → ZMod 2) (i : Fin k) (hi0 : i ≠ rckSUc_e hk 0)
    (hi1 : i ≠ rckSUc_e hk 1) (j : Fin k) :
    (rckSUc_M hk v * B) i j = 0 := by
  rw [rckSUc_M, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul]
  simp only [Matrix.add_apply, rckSUc_single_mul_apply]
  simp [hi0, hi1]

theorem rckSUc_B_mul_M_corner0 (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (τ : SUF ≃+* SUF) (v : Fin 4 → ZMod 2) (a : Fin 2) :
    (B * (rckSUc_M hk v).map τ) (rckSUc_e hk a) (rckSUc_e' hk 0)
      = (rckSUc_g hk B * (rckSUc_A v).map τ) a 0 := by
  rw [rckSUc_B_mul_M_rev0]
  simp [rckSUc_g, Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_two, rckSUc_A,
    Matrix.map_apply, Matrix.cons_val_zero, Matrix.cons_val_succ]

theorem rckSUc_B_mul_M_corner1 (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (τ : SUF ≃+* SUF) (v : Fin 4 → ZMod 2) (a : Fin 2) :
    (B * (rckSUc_M hk v).map τ) (rckSUc_e hk a) (rckSUc_e' hk 1)
      = (rckSUc_g hk B * (rckSUc_A v).map τ) a 1 := by
  rw [rckSUc_B_mul_M_rev1]
  simp [rckSUc_g, Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_two, rckSUc_A,
    Matrix.map_apply, Matrix.cons_val_zero, Matrix.cons_val_succ]

theorem rckSUc_M_mul_B_corner0 (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (v : Fin 4 → ZMod 2) (b : Fin 2) :
    (rckSUc_M hk v * B) (rckSUc_e hk 0) (rckSUc_e' hk b)
      = (rckSUc_A v * rckSUc_h hk B) 0 b := by
  rw [rckSUc_M_mul_B_row0]
  simp [rckSUc_h, Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_two, rckSUc_A,
    Matrix.cons_val_zero, Matrix.cons_val_succ]

theorem rckSUc_M_mul_B_corner1 (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (v : Fin 4 → ZMod 2) (b : Fin 2) :
    (rckSUc_M hk v * B) (rckSUc_e hk 1) (rckSUc_e' hk b)
      = (rckSUc_A v * rckSUc_h hk B) 1 b := by
  rw [rckSUc_M_mul_B_row1]
  simp [rckSUc_h, Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_two, rckSUc_A,
    Matrix.cons_val_zero, Matrix.cons_val_succ]

theorem rckSUc_corner_comm (hk : 4 ≤ k) (B : GL (Fin k) SUF) (τ : SUF ≃+* SUF)
    (hB : conjTr SUσ (B : Matrix (Fin k) (Fin k) SUF) * rckSUc_J k *
      (B : Matrix (Fin k) (Fin k) SUF) = rckSUc_J k)
    (hBN : (B : Matrix (Fin k) (Fin k) SUF) * rckSUc_N hk = rckSUc_N hk *
      (B : Matrix (Fin k) (Fin k) SUF)) (v : Fin 4 → ZMod 2) :
    (B : Matrix (Fin k) (Fin k) SUF) * (rckSUc_M hk v).map τ
      = rckSUc_M hk ((rckSUc_psi hk B τ hB hBN : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v)
        * (B : Matrix (Fin k) (Fin k) SUF) := by
  have hkey := rckSUc_g_mul_A_tau hk B τ hB hBN v
  ext i j
  by_cases hi0 : i = rckSUc_e hk 0
  · subst hi0
    by_cases hj0 : j = rckSUc_e' hk 0
    · subst hj0
      rw [rckSUc_B_mul_M_corner0 hk (B : Matrix (Fin k) (Fin k) SUF) τ v 0,
        rckSUc_M_mul_B_corner0 hk (B : Matrix (Fin k) (Fin k) SUF)
          ((rckSUc_psi hk B τ hB hBN : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) 0, hkey]
    · by_cases hj1 : j = rckSUc_e' hk 1
      · subst hj1
        rw [rckSUc_B_mul_M_corner1 hk (B : Matrix (Fin k) (Fin k) SUF) τ v 0,
          rckSUc_M_mul_B_corner0 hk (B : Matrix (Fin k) (Fin k) SUF)
            ((rckSUc_psi hk B τ hB hBN : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) 1, hkey]
      · rw [rckSUc_B_mul_M_off hk (B : Matrix (Fin k) (Fin k) SUF) τ v
            (rckSUc_e hk 0) j hj0 hj1,
          rckSUc_M_mul_B_row0 hk (B : Matrix (Fin k) (Fin k) SUF)
            ((rckSUc_psi hk B τ hB hBN : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) j,
          (rckSUc_B_row_of_ne hk (B : Matrix (Fin k) (Fin k) SUF) hBN j hj0 hj1).1,
          (rckSUc_B_row_of_ne hk (B : Matrix (Fin k) (Fin k) SUF) hBN j hj0 hj1).2,
          mul_zero, mul_zero, add_zero]
  · by_cases hi1 : i = rckSUc_e hk 1
    · subst hi1
      by_cases hj0 : j = rckSUc_e' hk 0
      · subst hj0
        rw [rckSUc_B_mul_M_corner0 hk (B : Matrix (Fin k) (Fin k) SUF) τ v 1,
          rckSUc_M_mul_B_corner1 hk (B : Matrix (Fin k) (Fin k) SUF)
            ((rckSUc_psi hk B τ hB hBN : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) 0, hkey]
      · by_cases hj1 : j = rckSUc_e' hk 1
        · subst hj1
          rw [rckSUc_B_mul_M_corner1 hk (B : Matrix (Fin k) (Fin k) SUF) τ v 1,
            rckSUc_M_mul_B_corner1 hk (B : Matrix (Fin k) (Fin k) SUF)
              ((rckSUc_psi hk B τ hB hBN : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) 1, hkey]
        · rw [rckSUc_B_mul_M_off hk (B : Matrix (Fin k) (Fin k) SUF) τ v
              (rckSUc_e hk 1) j hj0 hj1,
            rckSUc_M_mul_B_row1 hk (B : Matrix (Fin k) (Fin k) SUF)
              ((rckSUc_psi hk B τ hB hBN : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) j,
            (rckSUc_B_row_of_ne hk (B : Matrix (Fin k) (Fin k) SUF) hBN j hj0 hj1).1,
            (rckSUc_B_row_of_ne hk (B : Matrix (Fin k) (Fin k) SUF) hBN j hj0 hj1).2,
            mul_zero, mul_zero, add_zero]
    · rw [rckSUc_B_mul_M_zero_left hk (B : Matrix (Fin k) (Fin k) SUF) hBN τ v i hi0 hi1 j,
        rckSUc_M_mul_B_off hk (B : Matrix (Fin k) (Fin k) SUF)
          ((rckSUc_psi hk B τ hB hBN : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) i hi0 hi1 j]

theorem rckSUc_conj_corner (hk : 4 ≤ k) (B : GL (Fin k) SUF) (τ : SUF ≃+* SUF)
    (hB : conjTr SUσ (B : Matrix (Fin k) (Fin k) SUF) * rckSUc_J k *
      (B : Matrix (Fin k) (Fin k) SUF) = rckSUc_J k)
    (hBN : (B : Matrix (Fin k) (Fin k) SUF) * rckSUc_N hk = rckSUc_N hk *
      (B : Matrix (Fin k) (Fin k) SUF)) (v : Fin 4 → ZMod 2) :
    (B : Matrix (Fin k) (Fin k) SUF) * (suCorner hk v).map τ
      = suCorner hk ((rckSUc_psi hk B τ hB hBN : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v)
        * (B : Matrix (Fin k) (Fin k) SUF) := by
  rw [rckSUc_M_eq_suCorner, rckSUc_M_eq_suCorner, rckSUc_map_add, rckSUc_map_one_k hk,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, rckSUc_corner_comm]

theorem rckSUc_conj_corner_Binv (hk : 4 ≤ k) (B : GL (Fin k) SUF) (τ : SUF ≃+* SUF)
    (hB : conjTr SUσ (B : Matrix (Fin k) (Fin k) SUF) * rckSUc_J k *
      (B : Matrix (Fin k) (Fin k) SUF) = rckSUc_J k)
    (hBN : (B : Matrix (Fin k) (Fin k) SUF) * rckSUc_N hk = rckSUc_N hk *
      (B : Matrix (Fin k) (Fin k) SUF)) (v : Fin 4 → ZMod 2) :
    (B : Matrix (Fin k) (Fin k) SUF) * (suCorner hk v).map τ *
        ((B⁻¹ : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF)
      = suCorner hk ((rckSUc_psi hk B τ hB hBN : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) := by
  rw [rckSUc_conj_corner hk B τ hB hBN v, Matrix.mul_assoc,
    show (B : Matrix (Fin k) (Fin k) SUF) * ((B⁻¹ : GL (Fin k) SUF) : Matrix _ _ _) = 1 from by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one],
    Matrix.mul_one]

theorem rckSUc_det_map (τ : SUF ≃+* SUF) (M : Matrix (Fin 2) (Fin 2) SUF) :
    (M.map τ).det = τ M.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [Matrix.map_apply, map_sub, map_mul]

theorem rckSUc_det_gstar (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF) :
    (rckSUc_gstar hk B).det = SUσ (rckSUc_g hk B).det := by
  rw [rckSUc_gstar, conjTr, Matrix.det_transpose, rckSUc_det_map]

theorem rckSUc_tau_alpha (τ : SUF ≃+* SUF) (z : ZMod 2) :
    τ (rckSUc_alpha z) = rckSUc_alpha z := by
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) z with h | h <;>
    rw [h] <;> simp [rckSUc_alpha]

theorem rckSUc_det_g_ne_zero (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (hB : conjTr SUσ B * rckSUc_J k * B = rckSUc_J k)
    (hBN : B * rckSUc_N hk = rckSUc_N hk * B) : (rckSUc_g hk B).det ≠ 0 := by
  have h := congrArg Matrix.det (rckSUc_gstar_mul_h hk B hB hBN)
  rw [Matrix.det_mul, Matrix.det_one] at h
  have hne : (rckSUc_gstar hk B).det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact zero_ne_one h
  rw [rckSUc_det_gstar] at hne
  intro hg
  exact hne (by rw [hg]; exact map_zero SUσ)

theorem rckSUc_det_g_mul_sigma (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (hB : conjTr SUσ B * rckSUc_J k * B = rckSUc_J k)
    (hBN : B * rckSUc_N hk = rckSUc_N hk * B) :
    (rckSUc_g hk B).det * SUσ (rckSUc_g hk B).det = 1 := by
  haveI : Fintype SUF := Fintype.ofFinite SUF
  have hne := rckSUc_det_g_ne_zero hk B hB hBN
  have h3 : (rckSUc_g hk B).det ^ 3 = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one (rckSUc_g hk B).det hne
    rw [← Nat.card_eq_fintype_card, rckSUc_card] at h
    simpa using h
  rw [rckSUc_sigma_apply,
    show (rckSUc_g hk B).det * (rckSUc_g hk B).det ^ 2 = (rckSUc_g hk B).det ^ 3 by ring]
  exact h3

theorem rckSUc_beta_mul_sigma (v : Fin 4 → ZMod 2) :
    rckSUc_beta v * SUσ (rckSUc_beta v)
      = rckSUc_alpha (v 1) * rckSUc_alpha (v 1)
        + rckSUc_alpha (v 1) * rckSUc_alpha (v 2)
        + rckSUc_alpha (v 2) * rckSUc_alpha (v 2) := by
  simp only [rckSUc_beta, map_add, map_mul, rckSUc_sigma_alpha, rckSUc_sigma_omega]
  linear_combination
    (rckSUc_alpha (v 2) * rckSUc_alpha (v 2)) * suOmega_spec
    + (1 : SUF) * rckSUc_two (rckSUc_alpha (v 1) * rckSUc_alpha (v 2) * suOmega)
    + (-1 : SUF) * rckSUc_two (rckSUc_alpha (v 2) * rckSUc_alpha (v 2))

theorem rckSUc_A_apply_00 (v : Fin 4 → ZMod 2) :
    rckSUc_A v 0 0 = rckSUc_alpha (v 0) := rfl

theorem rckSUc_A_apply_01 (v : Fin 4 → ZMod 2) :
    rckSUc_A v 0 1 = rckSUc_beta v := rfl

theorem rckSUc_A_apply_10 (v : Fin 4 → ZMod 2) :
    rckSUc_A v 1 0 = SUσ (rckSUc_beta v) := rfl

theorem rckSUc_A_apply_11 (v : Fin 4 → ZMod 2) :
    rckSUc_A v 1 1 = rckSUc_alpha (v 3) := rfl

theorem rckSUc_det_A (v : Fin 4 → ZMod 2) :
    (rckSUc_A v).det = rckSUc_alpha (s5q v) := by
  have h00 : rckSUc_A v 0 0 = rckSUc_alpha (v 0) := rfl
  have h01 : rckSUc_A v 0 1 = rckSUc_beta v := rfl
  have h10 : rckSUc_A v 1 0 = SUσ (rckSUc_beta v) := rfl
  have h11 : rckSUc_A v 1 1 = rckSUc_alpha (v 3) := rfl
  rw [Matrix.det_fin_two, h00, h01, h10, h11]
  rw [sub_eq_add_neg,
    neg_eq_of_add_eq_zero_left (rckSUc_two (rckSUc_beta v * SUσ (rckSUc_beta v)))]
  rw [rckSUc_beta_mul_sigma, s5q]
  simp only [map_add, map_mul]

theorem rckSUc_det_psi (hk : 4 ≤ k) (B : GL (Fin k) SUF) (τ : SUF ≃+* SUF)
    (hB : conjTr SUσ (B : Matrix (Fin k) (Fin k) SUF) * rckSUc_J k *
      (B : Matrix (Fin k) (Fin k) SUF) = rckSUc_J k)
    (hBN : (B : Matrix (Fin k) (Fin k) SUF) * rckSUc_N hk = rckSUc_N hk *
      (B : Matrix (Fin k) (Fin k) SUF)) (v : Fin 4 → ZMod 2) :
    (rckSUc_A ((rckSUc_psi hk B τ hB hBN : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v)).det
      = (rckSUc_A v).det := by
  rw [rckSUc_A_psi hk B τ hB hBN v, Matrix.det_mul, Matrix.det_mul, rckSUc_det_map,
    rckSUc_det_A v, rckSUc_tau_alpha, rckSUc_det_gstar,
    show (rckSUc_g hk (B : Matrix (Fin k) (Fin k) SUF)).det
        * (rckSUc_alpha (s5q v) * SUσ (rckSUc_g hk (B : Matrix (Fin k) (Fin k) SUF)).det)
      = rckSUc_alpha (s5q v)
        * ((rckSUc_g hk (B : Matrix (Fin k) (Fin k) SUF)).det
          * SUσ (rckSUc_g hk (B : Matrix (Fin k) (Fin k) SUF)).det) by ring,
    rckSUc_det_g_mul_sigma hk (B : Matrix (Fin k) (Fin k) SUF) hB hBN, mul_one]

theorem rckSUc_q_preserved (hk : 4 ≤ k) (B : GL (Fin k) SUF) (τ : SUF ≃+* SUF)
    (hB : conjTr SUσ (B : Matrix (Fin k) (Fin k) SUF) * rckSUc_J k *
      (B : Matrix (Fin k) (Fin k) SUF) = rckSUc_J k)
    (hBN : (B : Matrix (Fin k) (Fin k) SUF) * rckSUc_N hk = rckSUc_N hk *
      (B : Matrix (Fin k) (Fin k) SUF)) (v : Fin 4 → ZMod 2) :
    s5q ((rckSUc_psi hk B τ hB hBN : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) = s5q v := by
  apply rckSUc_alpha_inj
  rw [show rckSUc_alpha (s5q ((rckSUc_psi hk B τ hB hBN :
        Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v))
      = (rckSUc_A ((rckSUc_psi hk B τ hB hBN :
        Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v)).det from (rckSUc_det_A _).symm,
    show rckSUc_alpha (s5q v) = (rckSUc_A v).det from (rckSUc_det_A v).symm]
  exact rckSUc_det_psi hk B τ hB hBN v

theorem rckSUc_psi_fixed_R (hk : 4 ≤ k) (B : GL (Fin k) SUF) (τ : SUF ≃+* SUF)
    (hB : conjTr SUσ (B : Matrix (Fin k) (Fin k) SUF) * rckSUc_J k *
      (B : Matrix (Fin k) (Fin k) SUF) = rckSUc_J k)
    (hBN : (B : Matrix (Fin k) (Fin k) SUF) * rckSUc_N hk = rckSUc_N hk *
      (B : Matrix (Fin k) (Fin k) SUF))
    (hr : (B : Matrix (Fin k) (Fin k) SUF) *
      ((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF).map τ *
        ((B⁻¹ : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) =
      ((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF)) :
    (rckSUc_psi hk B τ hB hBN : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec s5R = s5R := by
  have hv : suCorner hk ((rckSUc_psi hk B τ hB hBN : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec s5R)
      = suCorner hk s5R := by
    rw [← rckSUc_conj_corner_Binv hk B τ hB hBN s5R]
    have hsu : (suCorner hk s5R : Matrix (Fin k) (Fin k) SUF)
        = ((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) := by
      rw [rckSUc_M_eq_suCorner, rckSUc_M_s5R]
      exact (rckSUc_suR_eq hk).symm
    rw [hsu]
    have hτ : (((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF)).map τ
        = ((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) := by
      rw [rckSUc_suR_eq hk, rckSUc_map_add, rckSUc_map_one_k hk, rckSUc_N_map]
    simpa [hτ] using hr
  apply suZ_injective hk
  apply Subtype.ext
  apply Units.ext
  rw [suZ_val, suZ_val]
  exact hv

theorem rckSUc_map_refl (M : Matrix (Fin 2) (Fin 2) SUF) :
    M.map (RingEquiv.refl SUF) = M := by
  ext i j
  simp [Matrix.map_apply]

theorem rckSUc_s5tau_e0 : (s5tau : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec ![1, 0, 0, 0]
    = ![1, 0, 0, 0] := by
  decide +kernel

theorem rckSUc_s5tau_R : (s5tau : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec s5R = s5R := by
  decide +kernel

theorem rckSUc_s5tau_e2 : (s5tau : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec ![0, 0, 1, 0]
    = ![0, 1, 1, 0] := by
  decide +kernel

theorem rckSUc_g_Ae0_gstar_11 (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF) :
    (rckSUc_g hk B * rckSUc_A ![1, 0, 0, 0] * rckSUc_gstar hk B) 1 1
      = rckSUc_g hk B 1 0 * SUσ (rckSUc_g hk B 1 0) := by
  have h00 : rckSUc_A ![1, 0, 0, 0] 0 0 = 1 := by
    rw [rckSUc_A_apply_00]; simp [rckSUc_alpha]
  have h01 : rckSUc_A ![1, 0, 0, 0] 0 1 = 0 := by
    rw [rckSUc_A_apply_01]; simp [rckSUc_beta, rckSUc_alpha]
  have h10 : rckSUc_A ![1, 0, 0, 0] 1 0 = 0 := by
    rw [rckSUc_A_apply_10]; simp [rckSUc_beta, rckSUc_alpha]
  have h11 : rckSUc_A ![1, 0, 0, 0] 1 1 = 0 := by
    rw [rckSUc_A_apply_11]; simp [rckSUc_alpha]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, rckSUc_g, rckSUc_gstar,
    Matrix.submatrix_apply, conjTr_apply]
  rw [h00, h01, h10, h11]
  ring

theorem rckSUc_g_Pi_gstar_01 (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF) :
    (rckSUc_g hk B * rckSUc_A s5R * rckSUc_gstar hk B) 0 1
      = rckSUc_g hk B 0 0 * SUσ (rckSUc_g hk B 1 1)
        + rckSUc_g hk B 0 1 * SUσ (rckSUc_g hk B 1 0) := by
  have h00 : rckSUc_A s5R 0 0 = 0 := by
    rw [rckSUc_A_apply_00]; simp [rckSUc_alpha, s5R]
  have h01 : rckSUc_A s5R 0 1 = 1 := by
    rw [rckSUc_A_apply_01]; simp [rckSUc_beta, rckSUc_alpha, s5R]
  have h10 : rckSUc_A s5R 1 0 = 1 := by
    rw [rckSUc_A_apply_10]; simp [rckSUc_beta, rckSUc_alpha, s5R]
  have h11 : rckSUc_A s5R 1 1 = 0 := by
    rw [rckSUc_A_apply_11]; simp [rckSUc_alpha, s5R]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, rckSUc_g, rckSUc_gstar,
    Matrix.submatrix_apply, conjTr_apply]
  rw [h00, h01, h10, h11]
  ring

theorem rckSUc_g_Ae2_gstar_01 (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF) :
    (rckSUc_g hk B * rckSUc_A ![0, 0, 1, 0] * rckSUc_gstar hk B) 0 1
      = rckSUc_g hk B 0 0 * suOmega * SUσ (rckSUc_g hk B 1 1)
        + rckSUc_g hk B 0 1 * SUσ suOmega * SUσ (rckSUc_g hk B 1 0) := by
  have h00 : rckSUc_A ![0, 0, 1, 0] 0 0 = 0 := by
    rw [rckSUc_A_apply_00]; simp [rckSUc_alpha]
  have h01 : rckSUc_A ![0, 0, 1, 0] 0 1 = suOmega := by
    rw [rckSUc_A_apply_01]; simp [rckSUc_beta, rckSUc_alpha]
  have h10 : rckSUc_A ![0, 0, 1, 0] 1 0 = SUσ suOmega := by
    rw [rckSUc_A_apply_10]; simp [rckSUc_beta, rckSUc_alpha]
  have h11 : rckSUc_A ![0, 0, 1, 0] 1 1 = 0 := by
    rw [rckSUc_A_apply_11]; simp [rckSUc_alpha]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, rckSUc_g, rckSUc_gstar,
    Matrix.submatrix_apply, conjTr_apply]
  rw [h00, h01, h10, h11]
  ring

theorem rckSUc_ne_tau (hk : 4 ≤ k) (B : GL (Fin k) SUF) (τ : SUF ≃+* SUF)
    (hB : conjTr SUσ (B : Matrix (Fin k) (Fin k) SUF) * rckSUc_J k *
      (B : Matrix (Fin k) (Fin k) SUF) = rckSUc_J k)
    (hBN : (B : Matrix (Fin k) (Fin k) SUF) * rckSUc_N hk = rckSUc_N hk *
      (B : Matrix (Fin k) (Fin k) SUF)) (hτ : τ = RingEquiv.refl SUF) :
    rckSUc_psi hk B τ hB hBN ≠ s5tau := by
  intro hψ
  have hA : ∀ v : Fin 4 → ZMod 2,
      rckSUc_A ((rckSUc_psi hk B τ hB hBN : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v)
        = rckSUc_g hk (B : Matrix (Fin k) (Fin k) SUF) * rckSUc_A v
          * rckSUc_gstar hk (B : Matrix (Fin k) (Fin k) SUF) := by
    intro v
    rw [rckSUc_A_psi hk B τ hB hBN v, hτ, rckSUc_map_refl]
    simp only [Matrix.mul_assoc]
  have h0 := hA ![1, 0, 0, 0]
  rw [hψ, rckSUc_s5tau_e0] at h0
  have hg10 : rckSUc_g hk (B : Matrix (Fin k) (Fin k) SUF) 1 0 = 0 := by
    have h := congrFun (congrFun h0 1) 1
    rw [rckSUc_g_Ae0_gstar_11] at h
    have hz : rckSUc_A ![1, 0, 0, 0] 1 1 = 0 := by simp [rckSUc_A, rckSUc_beta]
    rw [hz] at h
    rcases mul_eq_zero.1 h.symm with hh | hh
    · exact hh
    · exact SUσ.injective (hh.trans (map_zero SUσ).symm)
  have hR := hA s5R
  rw [hψ, rckSUc_s5tau_R] at hR
  have hps : rckSUc_g hk (B : Matrix (Fin k) (Fin k) SUF) 0 0
      * SUσ (rckSUc_g hk (B : Matrix (Fin k) (Fin k) SUF) 1 1) = 1 := by
    have h := congrFun (congrFun hR 0) 1
    rw [rckSUc_g_Pi_gstar_01, hg10] at h
    have hz : rckSUc_A s5R 0 1 = 1 := by simp [rckSUc_A, rckSUc_beta, s5R]
    rw [hz] at h
    simpa [map_zero, mul_zero, add_zero] using h.symm
  have hE2 := hA ![0, 0, 1, 0]
  rw [hψ, rckSUc_s5tau_e2] at hE2
  have hw : SUσ suOmega = suOmega := by
    have h := congrFun (congrFun hE2 0) 1
    rw [rckSUc_g_Ae2_gstar_01, hg10] at h
    have hz : rckSUc_A ![0, 1, 1, 0] 0 1 = SUσ suOmega := by
      rw [rckSUc_A_apply_01, rckSUc_sigma_omega]
      simp [rckSUc_beta, rckSUc_alpha]
      ring
    rw [hz] at h
    simp only [map_zero, mul_zero, add_zero] at h
    have h1 : rckSUc_g hk (B : Matrix (Fin k) (Fin k) SUF) 0 0 * suOmega
        * SUσ (rckSUc_g hk (B : Matrix (Fin k) (Fin k) SUF) 1 1) = suOmega := by
      rw [show rckSUc_g hk (B : Matrix (Fin k) (Fin k) SUF) 0 0 * suOmega
            * SUσ (rckSUc_g hk (B : Matrix (Fin k) (Fin k) SUF) 1 1)
          = suOmega * (rckSUc_g hk (B : Matrix (Fin k) (Fin k) SUF) 0 0
            * SUσ (rckSUc_g hk (B : Matrix (Fin k) (Fin k) SUF) 1 1)) by ring,
        hps, mul_one]
    rw [h1] at h
    exact h
  exact rckSUc_omega_ne_sigma_omega hw.symm

end CFSG.StandardType.RCKK1IIISU
