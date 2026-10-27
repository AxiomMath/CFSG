module

public import CFSG.Quasithin.Vol2.Ch3E213MOLB4

public section

namespace CFSG.Quasithin.Ch3E213M.OLB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
open scoped MatrixGroups

@[expose] noncomputable def u₁ : SL(3, GaloisField 3 1) :=
  ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem coe_u₁ : ((u₁ : SL(3, GaloisField 3 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) =
    !![1, 0, 1; 0, 1, 0; 0, 0, 1] := rfl

theorem u₁_cube : u₁ * u₁ * u₁ = 1 := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_u₁, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  linear_combination three_eq_zero_gf3

theorem u₁_ne_one : u₁ ≠ 1 := by
  intro h
  have h1 := congrArg (fun y : SL(3, GaloisField 3 1) =>
    (y : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) 0 2) h
  simp [coe_u₁] at h1

theorem rootInv_conj_u₁ :
    Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num) * u₁ *
      Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num) = u₁⁻¹ := by
  refine eq_inv_of_mul_eq_one_left (Subtype.ext ?_)
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_u₁, coe_rootInv_three,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem commute_u₁_conj {q : SL(3, GaloisField 3 1)}
    (hq : q * Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num) =
      Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num) * q) :
    u₁ * (q * u₁ * q⁻¹) = q * u₁ * q⁻¹ * u₁ := by
  have hqi : q⁻¹ * Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num) =
      Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num) * q⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hq, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨-, -, q20, -⟩ := isBlockDiag_of_commute_rootInv hq
  obtain ⟨-, -, r20, -⟩ := isBlockDiag_of_commute_rootInv hqi
  set Q := ((q : SL(3, GaloisField 3 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) with hQ
  set Qi := ((q⁻¹ : SL(3, GaloisField 3 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 3 1))
    with hQi
  set E : Matrix (Fin 3) (Fin 3) (GaloisField 3 1) := Matrix.single 0 2 1 with hE
  have hU : ((u₁ : SL(3, GaloisField 3 1)) : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) = 1 + E := by
    rw [coe_u₁, hE]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hQQi : Q * Qi = 1 := by
    rw [hQ, hQi, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hEQE : E * Q * E = 0 := by
    ext i j
    simp [hE, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, q20]
  have hEQiE : E * Qi * E = 0 := by
    ext i j
    simp [hE, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, r20]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, hU, ← hQ, ← hQi]
  have h1 : Q * (1 + E) * Qi = 1 + Q * E * Qi := by
    rw [mul_add, mul_one, add_mul, hQQi]
  rw [h1]
  have h2 : E * (Q * E * Qi) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hEQE, Matrix.zero_mul]
  have h3 : Q * E * Qi * E = 0 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc E, hEQiE, Matrix.mul_zero]
  calc (1 + E) * (1 + Q * E * Qi) = 1 + E + Q * E * Qi + E * (Q * E * Qi) := by noncomm_ring
    _ = 1 + E + Q * E * Qi + Q * E * Qi * E := by rw [h2, h3]
    _ = (1 + Q * E * Qi) * (1 + E) := by noncomm_ring

theorem exists_sq_eq {G : Type*} [Group G] {y z : G} (hy : ∃ n : ℕ, y ^ 2 ^ n = 1)
    (hy1 : y ≠ 1) (hyz : y ≠ z) (hinv : ∀ m : ℕ, y ^ m * y ^ m = 1 → y ^ m ≠ 1 → y ^ m = z) :
    ∃ m : ℕ, y ^ m * y ^ m = z := by
  classical
  set n₀ := Nat.find hy with hn₀
  have hspec : y ^ 2 ^ n₀ = 1 := Nat.find_spec hy
  have hn0 : n₀ ≠ 0 := by
    intro h
    rw [h, pow_zero, pow_one] at hspec
    exact hy1 hspec
  have hmin : y ^ 2 ^ (n₀ - 1) ≠ 1 := Nat.find_min hy (by omega)
  have hsq : y ^ 2 ^ (n₀ - 1) * y ^ 2 ^ (n₀ - 1) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (by omega), hspec]
  have hz := hinv _ hsq hmin
  by_cases h1 : n₀ = 1
  · rw [h1, Nat.sub_self, pow_zero, pow_one] at hz
    exact absurd hz hyz
  · refine ⟨2 ^ (n₀ - 2), ?_⟩
    rw [← pow_add, ← two_mul, ← pow_succ', show n₀ - 2 + 1 = n₀ - 1 by omega, hz]

end CFSG.Quasithin.Ch3E213M.OLB
