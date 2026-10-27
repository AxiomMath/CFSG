module

public import Certificates.Certificate113
public import Certificates.Certificate114
public import CFSG.LieType.Steinberg.Adjoint.Pairs

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint


theorem q2cF4_no_frame_five {σ : Fin 5 → Fin 5 → Fin Tag.F4.rank → ℤ} {κ : ℤ} (hκ : κ ≠ 0)
    (hneg : ∀ i j, σ j i = -σ i j) (hadd : ∀ i j k, σ i j + σ j k = σ i k)
    (hnorm : ∀ a b, a ≠ b → iform (σ a b) (σ a b) = 2 * κ) : False := by
  let γ : Fin 4 → Fin Tag.F4.rank → ℤ := ![σ 0 1, σ 1 2, σ 2 3, σ 3 4]
  have e02 : σ 0 2 = γ 0 + γ 1 := by
    rw [← hadd 0 1 2]; simp [γ]
  have e13 : σ 1 3 = γ 1 + γ 2 := by
    rw [← hadd 1 2 3]; simp [γ]
  have e24 : σ 2 4 = γ 2 + γ 3 := by
    rw [← hadd 2 3 4]; simp [γ]
  have e03 : σ 0 3 = γ 0 + γ 1 + γ 2 := by
    rw [← hadd 0 2 3, e02]; simp [γ]
  have e14 : σ 1 4 = γ 1 + γ 2 + γ 3 := by
    rw [← hadd 1 3 4, e13]; simp [γ]
  have e04 : σ 0 4 = γ 0 + γ 1 + γ 2 + γ 3 := by
    rw [← hadd 0 3 4, e03]; simp [γ]
  have h00 : iform (γ 0) (γ 0) = 2 * κ := by simpa [γ] using hnorm 0 1 (by decide)
  have h11 : iform (γ 1) (γ 1) = 2 * κ := by simpa [γ] using hnorm 1 2 (by decide)
  have h22 : iform (γ 2) (γ 2) = 2 * κ := by simpa [γ] using hnorm 2 3 (by decide)
  have h33 : iform (γ 3) (γ 3) = 2 * κ := by simpa [γ] using hnorm 3 4 (by decide)
  have h01 : iform (γ 0) (γ 1) = -κ := by
    have h := hnorm 0 2 (by decide)
    rw [e02] at h
    simp only [iform_add_left, iform_add_right] at h
    rw [iform_comm (γ 1) (γ 0), h00, h11] at h
    linarith
  have h12 : iform (γ 1) (γ 2) = -κ := by
    have h := hnorm 1 3 (by decide)
    rw [e13] at h
    simp only [iform_add_left, iform_add_right] at h
    rw [iform_comm (γ 2) (γ 1), h11, h22] at h
    linarith
  have h23 : iform (γ 2) (γ 3) = -κ := by
    have h := hnorm 2 4 (by decide)
    rw [e24] at h
    simp only [iform_add_left, iform_add_right] at h
    rw [iform_comm (γ 3) (γ 2), h22, h33] at h
    linarith
  have h02 : iform (γ 0) (γ 2) = 0 := by
    have h := hnorm 0 3 (by decide)
    rw [e03] at h
    simp only [iform_add_left, iform_add_right] at h
    rw [iform_comm (γ 1) (γ 0), iform_comm (γ 2) (γ 0), iform_comm (γ 2) (γ 1),
      h00, h11, h22, h01, h12] at h
    linarith
  have h13 : iform (γ 1) (γ 3) = 0 := by
    have h := hnorm 1 4 (by decide)
    rw [e14] at h
    simp only [iform_add_left, iform_add_right] at h
    rw [iform_comm (γ 2) (γ 1), iform_comm (γ 3) (γ 1), iform_comm (γ 3) (γ 2),
      h11, h22, h33, h12, h23] at h
    linarith
  have h03 : iform (γ 0) (γ 3) = 0 := by
    have h := hnorm 0 4 (by decide)
    rw [e04] at h
    simp only [iform_add_left, iform_add_right] at h
    rw [iform_comm (γ 1) (γ 0), iform_comm (γ 2) (γ 0), iform_comm (γ 3) (γ 0),
      iform_comm (γ 2) (γ 1), iform_comm (γ 3) (γ 1), iform_comm (γ 3) (γ 2),
      h00, h11, h22, h33, h01, h12, h23, h02, h13] at h
    linarith
  have h10 : iform (γ 1) (γ 0) = -κ := by rw [iform_comm (γ 1) (γ 0), h01]
  have h21 : iform (γ 2) (γ 1) = -κ := by rw [iform_comm (γ 2) (γ 1), h12]
  have h32 : iform (γ 3) (γ 2) = -κ := by rw [iform_comm (γ 3) (γ 2), h23]
  have h20 : iform (γ 2) (γ 0) = 0 := by rw [iform_comm (γ 2) (γ 0), h02]
  have h31 : iform (γ 3) (γ 1) = 0 := by rw [iform_comm (γ 3) (γ 1), h13]
  have h30 : iform (γ 3) (γ 0) = 0 := by rw [iform_comm (γ 3) (γ 0), h03]
  let G : Matrix (Fin 4) (Fin 4) ℤ := fun k l => iform (γ k) (γ l)
  let C : Matrix (Fin 4) (Fin 4) ℤ :=
    !![2, -1, 0, 0; -1, 2, -1, 0; 0, -1, 2, -1; 0, 0, -1, 2]
  have hGC : G = κ • C := by
    ext k l
    fin_cases k <;> fin_cases l <;>
      simp only [G, C, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons, Matrix.cons_val,
        Matrix.empty_val', Matrix.cons_val_fin_one] <;>
      simp [h00, h11, h22, h33, h01, h12, h23, h02, h13, h03, h10, h21, h32, h20, h31, h30]
        <;> ring
  have hCdet : C.det = 5 := by decide +kernel
  have hdetG : G.det = 5 * κ ^ 4 := by
    rw [hGC, Matrix.det_smul, hCdet, Fintype.card_fin]
    ring
  let M : Matrix (Fin 4) (Fin 4) ℤ := fun k j => γ k j
  let B : Matrix (Fin 4) (Fin 4) ℤ := Tag.symmetrizedCartan Tag.F4
  have hGMB : G = M * B * M.transpose := by
    ext k l
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    simp only [G, M, B, iform]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hBdet : B.det = 4 := by
    change (Tag.symmetrizedCartan Tag.F4).det = 4
    decide +kernel
  have hdetGMB : G.det = 4 * (M.det) ^ 2 := by
    rw [hGMB, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hBdet]
    ring
  have hmain : 5 * κ ^ 4 = 4 * (M.det) ^ 2 := by
    rw [← hdetG, hdetGMB]
  have hsq : IsSquare (5 * (κ ^ 2) ^ 2 : ℤ) := by
    refine ⟨2 * M.det, ?_⟩
    rw [show (5 : ℤ) * (κ ^ 2) ^ 2 = 5 * κ ^ 4 by ring, hmain]
    ring
  obtain ⟨-, hev⟩ := Int.isSquare_iff_nonneg_even_factorization.mp hsq
  have h5 : Even ((5 * (κ ^ 2) ^ 2 : ℤ).natAbs.factorization 5) := hev 5 Nat.prime_five
  have hna : κ.natAbs ≠ 0 := by simpa [Int.natAbs_eq_zero] using hκ
  have hnatAbs : (5 * (κ ^ 2) ^ 2 : ℤ).natAbs = 5 * κ.natAbs ^ 4 := by
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow]
    norm_num
    ring
  have hfact : (5 * κ.natAbs ^ 4).factorization 5 = 1 + 4 * κ.natAbs.factorization 5 := by
    rw [Nat.factorization_mul (by norm_num) (pow_ne_zero 4 hna), Nat.factorization_pow]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [Nat.Prime.factorization_self Nat.prime_five]
  rw [hnatAbs, hfact] at h5
  obtain ⟨m, hm⟩ := h5
  omega

end CFSG.StandardType
