module

public import CFSG.LinearAlgebra.LinearGroups.SLThreeRootGeneration
public import CFSG.RankThree.PartTwo.KFacts.AutPSL
public import CFSG.CharacterTheory.Semidihedral.FixedFieldData
public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient

public section

namespace CFSG.RankThree.PartTwo.KFacts.PSLThreeGraphField

open Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LinearAlgebra.SLThreeRootGeneration
open CFSG.Semidihedral.FixedFieldData

variable {K : Type} [Field K]

private lemma omega_sq_add_omega [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    ω ^ 2 + ω = 1 := by
  have h := congrArg (fun x : K => x + 1) hω
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] at h
  exact h

private lemma omega_sq_eq [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    ω ^ 2 = ω + 1 := by
  have h := omega_sq_add_omega hω
  calc ω ^ 2 = ω ^ 2 + ω + ω := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = (ω ^ 2 + ω) + ω := by ring
    _ = 1 + ω := by rw [h]
    _ = ω + 1 := by ring

private lemma omega_cube [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 := by
  have h2 := omega_sq_eq hω
  calc ω ^ 3 = ω * ω ^ 2 := by ring
    _ = ω * (ω + 1) := by rw [h2]
    _ = ω ^ 2 + ω := by ring
    _ = 1 := omega_sq_add_omega hω

private lemma omega_ne_one [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 1 := by
  intro h
  have h2 := omega_sq_add_omega hω
  rw [h] at h2
  simp only [one_pow] at h2
  have h3 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rw [h3] at h2
  exact zero_ne_one h2

private lemma omega_ne_zero [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 0 := by
  intro h
  rw [h] at hω
  norm_num at hω

private lemma orderOf_omega [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    orderOf ω = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (omega_cube hω) (omega_ne_one hω)

private lemma omega_rearrange₁ [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    ω + 1 + ω ^ 2 = 0 := by
  linear_combination hω

private lemma omega_rearrange₂ [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    1 + (ω + ω ^ 2) = 0 := by
  linear_combination hω

private lemma map_omega_sq [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {σ : K ≃+* K}
    (hσω : σ ω = ω ^ 2) : σ (ω ^ 2) = ω := by
  rw [map_pow, hσω]
  calc (ω ^ 2) ^ 2 = ω ^ 4 := by ring
    _ = ω * ω ^ 3 := by ring
    _ = ω := by rw [omega_cube hω, mul_one]

private lemma omega_pow_odd [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {m : ℕ}
    (hm : Odd m) : ω ^ (2 ^ m) = ω ^ 2 := by
  have h2mod : 2 ^ m % 3 = 2 := by
    obtain ⟨t, rfl⟩ := hm
    rw [pow_succ, pow_mul, show 2 ^ 2 = 4 by norm_num]
    have h4 : 4 ^ t % 3 = 1 := by rw [Nat.pow_mod]; norm_num
    rw [Nat.mul_mod, h4]
  have hdiv := Nat.div_add_mod (2 ^ m) 3
  have h3 : 3 * (2 ^ m / 3) + 2 = 2 ^ m := by
    simpa [h2mod] using hdiv
  calc ω ^ (2 ^ m) = ω ^ (3 * (2 ^ m / 3) + 2) := by rw [h3]
    _ = (ω ^ 3) ^ (2 ^ m / 3) * ω ^ 2 := by rw [pow_add, pow_mul]
    _ = ω ^ 2 := by rw [omega_cube hω, one_pow, one_mul]

private lemma det_changeOfBasisMatrix [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    (!![1, 0, ω; 1, 0, ω ^ 2; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  have h := omega_sq_add_omega hω
  rw [Matrix.det_fin_three]
  simp [h, CharTwo.neg_eq]
  all_goals try ring_nf
  all_goals try simp [CharTwo.two_eq_zero, add_comm, h]

private lemma det_changeOfBasisInvMatrix [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    (!![ω ^ 2, ω, 0; 0, 0, 1; 1, 1, 0] : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  have h := omega_sq_add_omega hω
  rw [Matrix.det_fin_three]
  simp [h, CharTwo.neg_eq]
  all_goals try ring_nf
  all_goals try simp [CharTwo.two_eq_zero, add_comm, h]

@[expose] def changeOfBasis [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 0, ω; 1, 0, ω ^ 2; 0, 1, 0], by rw [det_changeOfBasisMatrix hω]⟩

private def changeOfBasisInv [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    SpecialLinearGroup (Fin 3) K :=
  ⟨!![ω ^ 2, ω, 0; 0, 0, 1; 1, 1, 0], by rw [det_changeOfBasisInvMatrix hω]⟩

private lemma changeOfBasisMatrix_mul_invMatrix [CharP K 2] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) :
    (!![1, 0, ω; 1, 0, ω ^ 2; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K) *
      !![ω ^ 2, ω, 0; 0, 0, 1; 1, 1, 0] = 1 := by
  have h := omega_sq_add_omega hω
  have h' : ω + ω ^ 2 = 1 := by rw [add_comm]; exact h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, h, h', CharTwo.add_self_eq_zero]
  all_goals try ring_nf
  all_goals try simp [CharTwo.two_eq_zero, add_comm]

private lemma changeOfBasisInvMatrix_mul_changeOfBasisMatrix [CharP K 2] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) :
    (!![ω ^ 2, ω, 0; 0, 0, 1; 1, 1, 0] : Matrix (Fin 3) (Fin 3) K) *
      !![1, 0, ω; 1, 0, ω ^ 2; 0, 1, 0] = 1 := by
  have h := omega_sq_add_omega hω
  have h' : ω + ω ^ 2 = 1 := by rw [add_comm]; exact h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, h, h', CharTwo.add_self_eq_zero]
  all_goals try ring_nf
  all_goals try simp [CharTwo.two_eq_zero, add_comm]

private lemma changeOfBasis_mul_inv [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    changeOfBasis hω * changeOfBasisInv hω = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  have h := congrFun (congrFun (changeOfBasisMatrix_mul_invMatrix hω) i) j
  simpa [changeOfBasis, changeOfBasisInv] using h

private lemma changeOfBasis_inv_mul [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    changeOfBasisInv hω * changeOfBasis hω = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  have h := congrFun (congrFun (changeOfBasisInvMatrix_mul_changeOfBasisMatrix hω) i) j
  simpa [changeOfBasis, changeOfBasisInv] using h

private lemma changeOfBasis_inv_eq [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    (changeOfBasis hω)⁻¹ = changeOfBasisInv hω :=
  inv_eq_of_mul_eq_one_right (changeOfBasis_mul_inv hω)

private def Jmat : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

private lemma det_Jmat [CharP K 2] : (Jmat (K := K)).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [Jmat, CharTwo.neg_eq]

private def JSL [CharP K 2] : SpecialLinearGroup (Fin 3) K := ⟨Jmat, det_Jmat⟩

private lemma JSL_coe [CharP K 2] :
    (JSL (K := K) : Matrix (Fin 3) (Fin 3) K) = Jmat := rfl

private lemma JSL_sq [CharP K 2] : JSL (K := K) * JSL (K := K) = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;>
    simp [JSL_coe, Jmat, Matrix.mul_apply, Fin.sum_univ_three]

private def U1 {ω : K} : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 1, ω; 0, 1, 1; 0, 0, 1], by
    rw [Matrix.det_fin_three]
    simp⟩

private lemma U1_coe {ω : K} :
    (U1 (K := K) (ω := ω) : Matrix (Fin 3) (Fin 3) K) =
      !![1, 1, ω; 0, 1, 1; 0, 0, 1] := rfl

private def U2 {ω : K} : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, ω, ω; 0, 1, ω ^ 2; 0, 0, 1], by
    rw [Matrix.det_fin_three]
    simp⟩

private lemma U2_coe {ω : K} :
    (U2 (K := K) (ω := ω) : Matrix (Fin 3) (Fin 3) K) =
      !![1, ω, ω; 0, 1, ω ^ 2; 0, 0, 1] := rfl

private lemma map_changeOfBasis_transpose [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {σ : K ≃+* K} (hσω : σ ω = ω ^ 2) :
    ((SpecialLinearGroup.map σ.toRingHom (changeOfBasis hω) : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)ᵀ =
      Jmat * (changeOfBasisInv hω : Matrix (Fin 3) (Fin 3) K) := by
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transpose_apply, Matrix.map_apply, changeOfBasis, changeOfBasisInv, Jmat,
      hσω, map_omega_sq hω hσω, Matrix.mul_apply, Fin.sum_univ_three]

private lemma map_changeOfBasisInv_transpose [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {σ : K ≃+* K} (hσω : σ ω = ω ^ 2) :
    ((SpecialLinearGroup.map σ.toRingHom (changeOfBasisInv hω) : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)ᵀ =
      (changeOfBasis hω : Matrix (Fin 3) (Fin 3) K) * Jmat := by
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transpose_apply, Matrix.map_apply, changeOfBasis, changeOfBasisInv, Jmat,
      hσω, map_omega_sq hω hσω, Matrix.mul_apply, Fin.sum_univ_three]

private lemma map_changeOfBasis_transpose_SL [CharP K 2] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {σ : K ≃+* K} (hσω : σ ω = ω ^ 2) :
    (SpecialLinearGroup.map σ.toRingHom (changeOfBasis hω)).transpose =
      JSL * changeOfBasisInv hω := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_mul, JSL_coe]
  exact congrFun (congrFun (map_changeOfBasis_transpose hω hσω) i) j

private lemma map_changeOfBasisInv_transpose_SL [CharP K 2] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {σ : K ≃+* K} (hσω : σ ω = ω ^ 2) :
    (SpecialLinearGroup.map σ.toRingHom (changeOfBasisInv hω)).transpose =
      changeOfBasis hω * JSL := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_mul, JSL_coe]
  exact congrFun (congrFun (map_changeOfBasisInv_transpose hω hσω) i) j

private lemma unitary_transvection02 [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {σ : K ≃+* K} (hσω : σ ω = ω ^ 2) :
    ((SpecialLinearGroup.map σ.toRingHom
        (SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (1 : K)) :
          SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ * Jmat *
      (SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (1 : K) :
        Matrix (Fin 3) (Fin 3) K) = Jmat := by
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transpose_apply, Matrix.map_apply, Jmat, SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_three]
  all_goals try ring_nf
  all_goals try simp [hω, omega_sq_add_omega hω, omega_cube hω, omega_rearrange₁ hω,
    omega_rearrange₂ hω, CharTwo.two_eq_zero, add_comm]

private lemma unitary_J [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {σ : K ≃+* K} (hσω : σ ω = ω ^ 2) :
    ((SpecialLinearGroup.map σ.toRingHom (JSL (K := K)) :
          SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ * Jmat *
      (JSL (K := K) : Matrix (Fin 3) (Fin 3) K) = Jmat := by
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transpose_apply, Matrix.map_apply, JSL_coe, Jmat,
      Matrix.mul_apply, Fin.sum_univ_three]
  all_goals try ring_nf
  all_goals try simp [hω, omega_sq_add_omega hω, omega_cube hω, omega_rearrange₁ hω,
    omega_rearrange₂ hω, CharTwo.two_eq_zero, add_comm]

private lemma unitary_U1 [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {σ : K ≃+* K} (hσω : σ ω = ω ^ 2) :
    ((SpecialLinearGroup.map σ.toRingHom (U1 (K := K) (ω := ω)) :
          SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ * Jmat *
      (U1 (K := K) (ω := ω) : Matrix (Fin 3) (Fin 3) K) = Jmat := by
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transpose_apply, Matrix.map_apply, U1, Jmat, hσω, map_omega_sq hω hσω,
      Matrix.mul_apply, Fin.sum_univ_three]
  all_goals try ring_nf
  all_goals try simp [hω, omega_sq_add_omega hω, omega_cube hω, omega_rearrange₁ hω,
    omega_rearrange₂ hω, CharTwo.two_eq_zero, add_comm]

private lemma unitary_U2 [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {σ : K ≃+* K} (hσω : σ ω = ω ^ 2) :
    ((SpecialLinearGroup.map σ.toRingHom (U2 (K := K) (ω := ω)) :
          SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ * Jmat *
      (U2 (K := K) (ω := ω) : Matrix (Fin 3) (Fin 3) K) = Jmat := by
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transpose_apply, Matrix.map_apply, U2, Jmat, hσω, map_omega_sq hω hσω,
      Matrix.mul_apply, Fin.sum_univ_three]
  all_goals try ring_nf
  all_goals try simp [hω, omega_sq_add_omega hω, omega_cube hω, omega_rearrange₁ hω,
    omega_rearrange₂ hω, CharTwo.two_eq_zero, add_comm]

private lemma unitary_SL_of_matrix [CharP K 2] {σ : K ≃+* K}
    (X : SpecialLinearGroup (Fin 3) K)
    (h : ((SpecialLinearGroup.map σ.toRingHom X : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)ᵀ * Jmat * (X : Matrix (Fin 3) (Fin 3) K) = Jmat) :
    (SpecialLinearGroup.map σ.toRingHom X).transpose * JSL * X = JSL := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have h' := congrFun (congrFun h i) j
  simpa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_transpose,
    JSL_coe] using h'

private lemma sl_transpose_mul (A B : SpecialLinearGroup (Fin 3) K) :
    (A * B).transpose = B.transpose * A.transpose := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_mul]
  rw [Matrix.transpose_mul]

private lemma sl_transpose_one : (1 : SpecialLinearGroup (Fin 3) K).transpose = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp [Matrix.SpecialLinearGroup.coe_transpose, Matrix.one_apply, eq_comm]

private lemma sl_transpose_inv (A : SpecialLinearGroup (Fin 3) K) :
    (A.transpose)⁻¹ = (A⁻¹).transpose := by
  have h : A.transpose * (A⁻¹).transpose = 1 := by
    rw [← sl_transpose_mul, inv_mul_cancel, sl_transpose_one]
  exact inv_eq_of_mul_eq_one_right h

private lemma sl_map_transpose (σ : K ≃+* K) (A : SpecialLinearGroup (Fin 3) K) :
    (SpecialLinearGroup.map σ.toRingHom A).transpose =
      SpecialLinearGroup.map σ.toRingHom A.transpose := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.map_apply_coe,
    Matrix.transpose_map, RingHom.mapMatrix_apply]

private lemma graphField_image_of_transpose_eq_inv (σ : K ≃+* K)
    (M M' : SpecialLinearGroup (Fin 3) K)
    (h : (SpecialLinearGroup.map σ.toRingHom M).transpose = M'⁻¹) :
    (fieldAut 3 K σ * dualAut 3 K) (proj 3 K M) = proj 3 K M' := by
  rw [MulAut.mul_apply, dualAut_proj, fieldAut_proj]
  have hM : SpecialLinearGroup.map σ.toRingHom (M⁻¹.transpose) = M' := by
    calc SpecialLinearGroup.map σ.toRingHom (M⁻¹.transpose)
        = (SpecialLinearGroup.map σ.toRingHom (M⁻¹)).transpose := (sl_map_transpose σ _).symm
      _ = ((SpecialLinearGroup.map σ.toRingHom M)⁻¹).transpose := by rw [map_inv]
      _ = ((SpecialLinearGroup.map σ.toRingHom M).transpose)⁻¹ := (sl_transpose_inv _).symm
      _ = (M'⁻¹)⁻¹ := by rw [h]
      _ = M' := inv_inv M'
  rw [hM]

private lemma graphField_fixed_of_unitary [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {σ : K ≃+* K} (hσω : σ ω = ω ^ 2)
    (C C' J X : SpecialLinearGroup (Fin 3) K)
    (hC : C * C' = 1) (hC' : C' * C = 1)
    (hCbar : (SpecialLinearGroup.map σ.toRingHom C).transpose = J * C')
    (hC'bar : (SpecialLinearGroup.map σ.toRingHom C').transpose = C * J)
    (hXbar : (SpecialLinearGroup.map σ.toRingHom X).transpose * J * X = J)
    (hJ : J * J = 1) :
    (fieldAut 3 K σ * dualAut 3 K) (proj 3 K (C * X * C')) = proj 3 K (C * X * C') := by
  refine graphField_image_of_transpose_eq_inv σ (C * X * C') (C * X * C') ?_
  have hprod : (SpecialLinearGroup.map σ.toRingHom (C * X * C')).transpose *
      (C * X * C') = 1 := by
    calc (SpecialLinearGroup.map σ.toRingHom (C * X * C')).transpose * (C * X * C')
        = ((SpecialLinearGroup.map σ.toRingHom C').transpose *
            (SpecialLinearGroup.map σ.toRingHom X).transpose *
            (SpecialLinearGroup.map σ.toRingHom C).transpose) * (C * X * C') := by
          rw [map_mul, map_mul, sl_transpose_mul, sl_transpose_mul]
          group
      _ = (C * J) * (SpecialLinearGroup.map σ.toRingHom X).transpose * (J * C') *
            (C * X * C') := by rw [hC'bar, hCbar]
      _ = C * J * (SpecialLinearGroup.map σ.toRingHom X).transpose * J * X * C' := by
          have h1 : (C * J) * (SpecialLinearGroup.map σ.toRingHom X).transpose * (J * C') *
                (C * X * C') =
              C * J * (SpecialLinearGroup.map σ.toRingHom X).transpose * J * (C' * C) *
                X * C' := by group
          rw [h1, hC']
          group
      _ = C * (J * ((SpecialLinearGroup.map σ.toRingHom X).transpose * J * X)) * C' := by
          group
      _ = C * (J * J) * C' := by rw [hXbar]
      _ = C * C' := by rw [hJ]; group
      _ = 1 := hC
  calc (SpecialLinearGroup.map σ.toRingHom (C * X * C')).transpose
      = (((SpecialLinearGroup.map σ.toRingHom (C * X * C')).transpose)⁻¹)⁻¹ := by rw [inv_inv]
    _ = (C * X * C')⁻¹ := by rw [inv_eq_of_mul_eq_one_right hprod]

private lemma inverse_mul_eq (C C' D : SpecialLinearGroup (Fin 3) K)
    (hC : C * C' = 1) (hC' : C' * C = 1) :
    (C * D * C')⁻¹ = C * D⁻¹ * C' := by
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_eq_of_mul_eq_one_right hC',
    inv_eq_of_mul_eq_one_right hC]
  group

private lemma det_diagSL [CharP K 2] {lam : K} (hlam : lam ≠ 0) :
    (diagonal ![lam, 1, lam⁻¹] : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [Matrix.det_diagonal, Fin.prod_univ_three]
  simp [hlam]

private def diagSL [CharP K 2] {lam : K} (hlam : lam ≠ 0) :
    SpecialLinearGroup (Fin 3) K :=
  ⟨diagonal ![lam, 1, lam⁻¹], det_diagSL hlam⟩

private lemma diagSL_coe [CharP K 2] {lam : K} (hlam : lam ≠ 0) :
    (diagSL (K := K) hlam : Matrix (Fin 3) (Fin 3) K) = diagonal ![lam, 1, lam⁻¹] := rfl

private lemma map_diagSL [CharP K 2] {σ : K ≃+* K} {lam : K} (hlam : lam ≠ 0)
    (hσlam : σ lam ≠ 0) :
    SpecialLinearGroup.map σ.toRingHom (diagSL (K := K) hlam) =
      diagSL (K := K) hσlam := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    simp [diagSL, Matrix.diagonal_apply, Matrix.map_apply]

private lemma diagSL_inv [CharP K 2] {lam : K} (hlam : lam ≠ 0) :
    (diagSL (K := K) hlam)⁻¹ = diagSL (K := K) (inv_ne_zero hlam) := by
  apply inv_eq_of_mul_eq_one_right
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;>
    simp [diagSL, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, hlam,
      Matrix.vecMul_diagonal]

private lemma JSL_conj_diag [CharP K 2] {lam : K} (hlam : lam ≠ 0) :
    JSL (K := K) * diagSL (K := K) hlam * JSL (K := K) =
      (diagSL (K := K) hlam)⁻¹ := by
  rw [diagSL_inv hlam]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [JSL_coe, Jmat, diagSL, Matrix.mul_apply, Matrix.mul_diagonal,
      Fin.sum_univ_three, Matrix.diagonal_apply, Matrix.vecMul_diagonal]
  all_goals try field_simp

private lemma diagSL_transpose [CharP K 2] {lam : K} (hlam : lam ≠ 0) :
    (diagSL (K := K) hlam).transpose = diagSL (K := K) hlam := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_transpose]
  change (diagonal ![lam, 1, lam⁻¹] : Matrix (Fin 3) (Fin 3) K).transpose i j =
    (diagonal ![lam, 1, lam⁻¹] : Matrix (Fin 3) (Fin 3) K) i j
  simp only [Matrix.transpose_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    rfl
  · simp [h, eq_comm]

private lemma graphField_image_diag_of_diagSL [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {σ : K ≃+* K} (hσω : σ ω = ω ^ 2) {lam : K} (hlam : lam ≠ 0)
    (hσlam : σ lam ≠ 0) :
    (fieldAut 3 K σ * dualAut 3 K)
        (proj 3 K (changeOfBasis hω * diagSL (K := K) hlam *
          (changeOfBasis hω)⁻¹)) =
      proj 3 K (changeOfBasis hω * diagSL (K := K) hσlam *
        (changeOfBasis hω)⁻¹) := by
  rw [changeOfBasis_inv_eq hω]
  refine graphField_image_of_transpose_eq_inv σ _ _ ?_
  have htrans : (SpecialLinearGroup.map σ.toRingHom
        (changeOfBasis hω * diagSL (K := K) hlam * changeOfBasisInv (K := K) hω)).transpose =
      (changeOfBasis hω * diagSL (K := K) hσlam * changeOfBasisInv (K := K) hω)⁻¹ := by
    calc (SpecialLinearGroup.map σ.toRingHom
          (changeOfBasis hω * diagSL (K := K) hlam * changeOfBasisInv (K := K) hω)).transpose
        = ((SpecialLinearGroup.map σ.toRingHom (changeOfBasisInv (K := K) hω)).transpose *
            (SpecialLinearGroup.map σ.toRingHom (diagSL (K := K) hlam)).transpose *
            (SpecialLinearGroup.map σ.toRingHom (changeOfBasis hω)).transpose) := by
          rw [map_mul, map_mul, sl_transpose_mul, sl_transpose_mul]
          group
      _ = ((changeOfBasis hω * JSL) * diagSL (K := K) hσlam *
            (JSL * changeOfBasisInv (K := K) hω)) := by
          rw [map_diagSL hlam hσlam, diagSL_transpose hσlam,
            map_changeOfBasisInv_transpose_SL hω hσω,
            map_changeOfBasis_transpose_SL hω hσω]
      _ = (changeOfBasis hω * diagSL (K := K) hσlam *
            changeOfBasisInv (K := K) hω)⁻¹ := by
          have h1 : (changeOfBasis hω * JSL) * diagSL (K := K) hσlam *
                (JSL * changeOfBasisInv (K := K) hω) =
              changeOfBasis hω * (JSL * diagSL (K := K) hσlam * JSL) *
                changeOfBasisInv (K := K) hω := by group
          rw [h1, JSL_conj_diag hσlam]
          exact (inverse_mul_eq _ _ _ (changeOfBasis_mul_inv hω)
            (changeOfBasis_inv_mul hω)).symm
  exact htrans

theorem graphField_fixed_transvection [CharP K 2] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {σ : K ≃+* K} (hσω : σ ω = ω ^ 2) :
    (fieldAut 3 K σ * dualAut 3 K)
        (proj 3 K (changeOfBasis hω *
          SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (1 : K) *
          (changeOfBasis hω)⁻¹)) =
      proj 3 K (changeOfBasis hω *
        SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (1 : K) *
        (changeOfBasis hω)⁻¹) := by
  rw [changeOfBasis_inv_eq hω]
  exact graphField_fixed_of_unitary hω hσω _ _ _ _
    (changeOfBasis_mul_inv hω) (changeOfBasis_inv_mul hω)
    (map_changeOfBasis_transpose_SL hω hσω) (map_changeOfBasisInv_transpose_SL hω hσω)
    (unitary_SL_of_matrix _ (unitary_transvection02 hω hσω)) (JSL_sq)

theorem graphField_fixed_J [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {σ : K ≃+* K} (hσω : σ ω = ω ^ 2)
    (J : SpecialLinearGroup (Fin 3) K)
    (hJcoe : (J : Matrix (Fin 3) (Fin 3) K) = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    (fieldAut 3 K σ * dualAut 3 K)
        (proj 3 K (changeOfBasis hω * J * (changeOfBasis hω)⁻¹)) =
      proj 3 K (changeOfBasis hω * J * (changeOfBasis hω)⁻¹) := by
  have hJ : J = JSL (K := K) := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [hJcoe, JSL_coe]
    rfl
  rw [hJ, changeOfBasis_inv_eq hω]
  exact graphField_fixed_of_unitary hω hσω _ _ _ _
    (changeOfBasis_mul_inv hω) (changeOfBasis_inv_mul hω)
    (map_changeOfBasis_transpose_SL hω hσω) (map_changeOfBasisInv_transpose_SL hω hσω)
    (unitary_SL_of_matrix _ (unitary_J hω hσω)) (JSL_sq)

theorem graphField_fixed_U1 [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {σ : K ≃+* K} (hσω : σ ω = ω ^ 2)
    (U : SpecialLinearGroup (Fin 3) K)
    (hUcoe : (U : Matrix (Fin 3) (Fin 3) K) = !![1, 1, ω; 0, 1, 1; 0, 0, 1]) :
    (fieldAut 3 K σ * dualAut 3 K)
        (proj 3 K (changeOfBasis hω * U * (changeOfBasis hω)⁻¹)) =
      proj 3 K (changeOfBasis hω * U * (changeOfBasis hω)⁻¹) := by
  have hU : U = U1 (K := K) (ω := ω) := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [hUcoe, U1_coe]
  rw [hU, changeOfBasis_inv_eq hω]
  exact graphField_fixed_of_unitary hω hσω _ _ _ _
    (changeOfBasis_mul_inv hω) (changeOfBasis_inv_mul hω)
    (map_changeOfBasis_transpose_SL hω hσω) (map_changeOfBasisInv_transpose_SL hω hσω)
    (unitary_SL_of_matrix _ (unitary_U1 hω hσω)) (JSL_sq)

theorem graphField_fixed_U2 [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {σ : K ≃+* K} (hσω : σ ω = ω ^ 2)
    (U : SpecialLinearGroup (Fin 3) K)
    (hUcoe : (U : Matrix (Fin 3) (Fin 3) K) = !![1, ω, ω; 0, 1, ω ^ 2; 0, 0, 1]) :
    (fieldAut 3 K σ * dualAut 3 K)
        (proj 3 K (changeOfBasis hω * U * (changeOfBasis hω)⁻¹)) =
      proj 3 K (changeOfBasis hω * U * (changeOfBasis hω)⁻¹) := by
  have hU : U = U2 (K := K) (ω := ω) := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [hUcoe, U2_coe]
  rw [hU, changeOfBasis_inv_eq hω]
  exact graphField_fixed_of_unitary hω hσω _ _ _ _
    (changeOfBasis_mul_inv hω) (changeOfBasis_inv_mul hω)
    (map_changeOfBasis_transpose_SL hω hσω) (map_changeOfBasisInv_transpose_SL hω hσω)
    (unitary_SL_of_matrix _ (unitary_U2 hω hσω)) (JSL_sq)

theorem graphField_image_diag [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {σ : K ≃+* K} (hσω : σ ω = ω ^ 2) {lam : K} (hlam : lam ≠ 0)
    (D D' : SpecialLinearGroup (Fin 3) K)
    (hD : (D : Matrix (Fin 3) (Fin 3) K) = diagonal ![lam, 1, lam⁻¹])
    (hD' : (D' : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![σ lam, 1, (σ lam)⁻¹]) :
    (fieldAut 3 K σ * dualAut 3 K)
        (proj 3 K (changeOfBasis hω * D * (changeOfBasis hω)⁻¹)) =
      proj 3 K (changeOfBasis hω * D' * (changeOfBasis hω)⁻¹) := by
  have hσlam : σ lam ≠ 0 := by
    intro h
    apply hlam
    apply σ.injective
    rw [h, map_zero]
  have hDsl : D = diagSL (K := K) hlam := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [hD, diagSL_coe]
  have hD'sl : D' = diagSL (K := K) hσlam := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [hD', diagSL_coe]
  rw [hDsl, hD'sl]
  exact graphField_image_diag_of_diagSL hω hσω hlam hσlam

theorem closure_fixed_union_diag_eq_top [Finite K] [CharP K 2] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {σ : K ≃+* K} (hσω : σ ω = ω ^ 2)
    {lam : K} (hlam : lam ≠ 0) (hclosure : Subfield.closure ({lam ^ 2} : Set K) = ⊤)
    (D : SpecialLinearGroup (Fin 3) K)
    (hD : (D : Matrix (Fin 3) (Fin 3) K) = diagonal ![lam, 1, lam⁻¹]) :
    Subgroup.closure ({x : projectiveSL 3 K |
        (fieldAut 3 K σ * dualAut 3 K) x = x} ∪
      {proj 3 K (changeOfBasis hω * D * (changeOfBasis hω)⁻¹)}) = ⊤ := by
  letI : Fintype K := Fintype.ofFinite K
  let f : SpecialLinearGroup (Fin 3) K →* projectiveSL 3 K :=
    (proj 3 K).comp (MulAut.conj (changeOfBasis hω)).toMonoidHom
  set Psub : Subgroup (projectiveSL 3 K) :=
    Subgroup.closure ({x : projectiveSL 3 K |
        (fieldAut 3 K σ * dualAut 3 K) x = x} ∪
      {proj 3 K (changeOfBasis hω * D * (changeOfBasis hω)⁻¹)}) with hPsub
  set S : Subgroup (SpecialLinearGroup (Fin 3) K) := Psub.comap f with hS
  have hf_surj : Function.Surjective f := by
    intro x
    obtain ⟨M, rfl⟩ := proj_surjective 3 K x
    refine ⟨(MulAut.conj (changeOfBasis hω)).symm M, ?_⟩
    change (proj 3 K) ((MulAut.conj (changeOfBasis hω))
      ((MulAut.conj (changeOfBasis hω)).symm M)) = proj 3 K M
    rw [MulEquiv.apply_symm_apply]
  have hfx : ∀ X : SpecialLinearGroup (Fin 3) K,
      f X = proj 3 K (changeOfBasis hω * X * (changeOfBasis hω)⁻¹) := by
    intro X
    simp [f, MulAut.conj_apply]
  have hX02 : SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) (1 : K) ∈ S := by
    rw [Subgroup.mem_comap, hfx]
    exact Subgroup.subset_closure (Or.inl (graphField_fixed_transvection hω hσω))
  have hJ : JSL (K := K) ∈ S := by
    rw [Subgroup.mem_comap, hfx]
    exact Subgroup.subset_closure (Or.inl (graphField_fixed_J hω hσω _ JSL_coe))
  have hU1 : U1 (K := K) (ω := ω) ∈ S := by
    rw [Subgroup.mem_comap, hfx]
    exact Subgroup.subset_closure (Or.inl (graphField_fixed_U1 hω hσω _ U1_coe))
  have hU2 : U2 (K := K) (ω := ω) ∈ S := by
    rw [Subgroup.mem_comap, hfx]
    exact Subgroup.subset_closure (Or.inl (graphField_fixed_U2 hω hσω _ U2_coe))
  have hDmem : D ∈ S := by
    rw [Subgroup.mem_comap, hfx]
    exact Subgroup.subset_closure (Or.inr rfl)
  have hStop : S = ⊤ :=
    CFSG.LinearAlgebra.SLThreeRootGeneration.eq_top_of_unitary_elements
      (ω := ω) (hω := hω) (lam := lam) (H := S)
      (hX02 := hX02) (J := JSL (K := K)) (hJcoe := JSL_coe) (hJ := hJ)
      (U1 := U1 (K := K) (ω := ω)) (hU1coe := U1_coe) (hU1 := hU1)
      (U2 := U2 (K := K) (ω := ω)) (hU2coe := U2_coe) (hU2 := hU2)
      (D := D) (hDcoe := hD) (hD := hDmem) (hclosure := hclosure)
  have hmap : Subgroup.map f S = Psub :=
    Subgroup.map_comap_eq_self_of_surjective hf_surj Psub
  rw [← hmap, hStop, Subgroup.map_top_of_surjective f hf_surj]

theorem frobenius_pow_apply [Finite K] [CharP K 2] (m : ℕ) (x : K) :
    ((frobeniusAut 2 K) ^ m) x = x ^ (2 ^ m) :=
  CFSG.LieType.Chevalley.ringAut_pow_apply_of_frobenius (K := K) (p := 2)
    (φ := frobeniusAut 2 K) (frobeniusAut_apply 2 K) m x

theorem frobenius_pow_apply_omega [Finite K] [CharP K 2] {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {m : ℕ} (hm : Odd m) : ((frobeniusAut 2 K) ^ m) ω = ω ^ 2 := by
  rw [frobenius_pow_apply]
  exact omega_pow_odd hω hm

private lemma two_pow_mod_three (i : ℕ) :
    2 ^ i % 3 = if i % 2 = 0 then 1 else 2 := by
  rcases Nat.even_or_odd i with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [show t + t = 2 * t by omega, pow_mul, show 2 ^ 2 = 4 by norm_num]
    have h4 : 4 ^ t % 3 = 1 := by rw [Nat.pow_mod]; norm_num
    rw [h4]
    simp
  · rw [pow_succ, pow_mul, show 2 ^ 2 = 4 by norm_num]
    have h4 : 4 ^ t % 3 = 1 := by rw [Nat.pow_mod]; norm_num
    rw [Nat.mul_mod, h4]
    simp

private lemma parity_of_two_pow_mod_three {i eps : ℕ} (heps : eps ≤ 1)
    (h : 2 ^ i % 3 = 2 ^ eps % 3) : i % 2 = eps := by
  interval_cases eps
  · rw [two_pow_mod_three] at h
    by_cases hi : i % 2 = 0
    · exact hi
    · simp [hi] at h
  · rw [two_pow_mod_three] at h
    simp at h
    by_cases hi : i % 2 = 0
    · simp [hi] at h
    · have hlt : i % 2 < 2 := Nat.mod_lt i (by norm_num)
      omega

private lemma dualAut_pow_eq_mod_two [CharP K 2] (i : ℕ) :
    (dualAut 3 K) ^ i = (dualAut 3 K) ^ (i % 2) := by
  have hδ2 : dualAut 3 K * dualAut 3 K = 1 := by
    obtain ⟨-, -, -, hdd, -, -⟩ := standard_automorphism_transport (K := K) (n := 3)
    exact hdd
  rcases Nat.even_or_odd i with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · have h2 : (t + t) % 2 = 0 := by omega
    rw [h2, pow_zero]
    rw [show t + t = 2 * t by omega, pow_mul, pow_two, hδ2, one_pow]
  · have h2 : (2 * t + 1) % 2 = 1 := by omega
    rw [h2, pow_one]
    rw [pow_succ, pow_mul, pow_two, hδ2, one_pow, one_mul]

private lemma frobenius_mul_dualAut_pow_two_mul [Finite K] [CharP K 2] (n : ℕ)
    (hK : Nat.card K = 2 ^ n) :
    (fieldAut 3 K (frobeniusAut 2 K) * dualAut 3 K) ^ (2 * n) = 1 := by
  let φ : K ≃+* K := frobeniusAut 2 K
  have hφorder : orderOf φ = n := frobeniusAut_order 2 n K hK
  have hφn : φ ^ n = 1 := by
    rw [← hφorder]
    exact pow_orderOf_eq_one φ
  have hfn : (fieldAut 3 K φ) ^ n = 1 := by
    rw [← map_pow, hφn, map_one]
  have hf2n : (fieldAut 3 K φ) ^ (2 * n) = 1 := by
    rw [mul_comm, pow_mul, hfn, one_pow]
  have hδ2 : dualAut 3 K * dualAut 3 K = 1 := by
    obtain ⟨-, -, -, hdd, -, -⟩ := standard_automorphism_transport (K := K) (n := 3)
    exact hdd
  have hδ2n : (dualAut 3 K) ^ (2 * n) = 1 := by
    rw [pow_mul, pow_two, hδ2, one_pow]
  have hcomm : Commute (fieldAut 3 K φ) (dualAut 3 K) :=
    standardFieldGraph_commute (fieldAut_mem_standardFieldGraph φ)
      dualAut_mem_standardFieldGraph
  rw [Commute.mul_pow hcomm (2 * n), hf2n, hδ2n, mul_one]

private lemma mem_zpowers_pow_of_pow_eq_one {G : Type*} [Group G] (h t : G) {n m k : ℕ}
    (hm : Odd m) (htwo : h ^ (2 * n) = 1)
    (ht : t ∈ Subgroup.zpowers h) (htk : t ^ (2 ^ k) = 1) :
    t ∈ Subgroup.zpowers (h ^ m) := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  let d : ℕ := orderOf h
  have hdvd : (d : ℤ) ∣ j * (2 ^ k : ℤ) := by
    have h1 : h ^ (j * ((2 ^ k : ℕ) : ℤ)) = 1 := by
      rw [_root_.zpow_mul, zpow_natCast]
      exact htk
    have h2 := (zpow_eq_one_iff_modEq (x := h)).mp h1
    have h3 := Int.modEq_iff_dvd.mp h2
    simpa using h3
  let s : ℕ := m.gcd d
  have hsm : s ∣ m := Nat.gcd_dvd_left m d
  have hsd : s ∣ d := Nat.gcd_dvd_right m d
  have hsodd : Odd s := Odd.of_dvd_nat hm hsm
  have hcop : s.Coprime (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hsodd)
  have hsmul : s ∣ j.natAbs * 2 ^ k := by
    have h4 : (s : ℤ) ∣ j * (2 ^ k : ℤ) := (Int.ofNat_dvd.mpr hsd).trans hdvd
    have h5 : s ∣ (j * (2 ^ k : ℤ)).natAbs := (Int.natCast_dvd).mp h4
    simpa [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] using h5
  have hsj : s ∣ j.natAbs := hcop.dvd_of_dvd_mul_right hsmul
  have hsjd : s ∣ j.gcd (d : ℤ) := by
    refine Int.dvd_gcd ?_ ?_
    · exact (Int.natCast_dvd).mpr hsj
    · exact (Int.ofNat_dvd.mpr hsd)
  have hle : Subgroup.zpowers (h ^ j) ≤ Subgroup.zpowers (h ^ m) := by
    rw [← zpow_natCast h m]
    rw [Subgroup.zpowers_le_zpowers_iff h j (m : ℤ)]
    change (m : ℤ).gcd (d : ℤ) ∣ j.gcd (d : ℤ)
    have hgd : (m : ℤ).gcd (d : ℤ) = s := by
      rw [Int.gcd_natCast_natCast]
    rw [hgd]
    exact hsjd
  exact Subgroup.zpowers_le.mp hle

theorem mem_zpowers_frobenius_mul_dualAut [Finite K] [CharP K 2] {n eps : ℕ}
    (hK : Nat.card K = 2 ^ n) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {σ : K ≃+* K} (heps : eps ≤ 1) (hσω : σ ω = ω ^ (2 ^ eps)) :
    fieldAut 3 K σ * dualAut 3 K ^ eps ∈
      Subgroup.zpowers (fieldAut 3 K (frobeniusAut 2 K) * dualAut 3 K) := by
  let φ : K ≃+* K := frobeniusAut 2 K
  have hφapply : ∀ x : K, φ x = x ^ 2 := fun x => frobeniusAut_apply 2 K x
  have hφorder : orderOf φ = n := frobeniusAut_order 2 n K hK
  have hφtop : (⊤ : Subgroup (K ≃+* K)) = Subgroup.zpowers φ := frobeniusAut_zpowers 2 K
  have hcard2 : 2 ≤ Nat.card K := by
    letI := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    rw [hn0, pow_zero] at hK
    omega
  have hσmem : σ ∈ Subgroup.zpowers φ := by
    rw [← hφtop]
    exact Subgroup.mem_top σ
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hσmem
  set i : ℕ := (j % (n : ℤ)).toNat with hi_def
  have hjn : 0 ≤ j % (n : ℤ) := Int.emod_nonneg j (by exact_mod_cast hn.ne')
  have hz : φ ^ (j % (n : ℤ)) = σ := by
    rw [← hφorder, zpow_mod_orderOf, hj]
  have hi : φ ^ i = σ := by
    rw [hi_def, ← zpow_natCast]
    rw [Int.toNat_of_nonneg hjn]
    exact hz
  have hφpow : (φ ^ i) ω = ω ^ (2 ^ i) :=
    CFSG.LieType.Chevalley.ringAut_pow_apply_of_frobenius (K := K) (p := 2) (φ := φ)
      hφapply i ω
  have hσpow : σ ω = ω ^ (2 ^ i) := by rw [← hi]; exact hφpow
  have hpowEq : ω ^ (2 ^ i) = ω ^ (2 ^ eps) := by rw [← hσpow]; exact hσω
  let u : Kˣ := Units.mk0 ω (omega_ne_zero hω)
  have huorder : orderOf u = 3 := by
    rw [← orderOf_units]
    change orderOf ω = 3
    exact orderOf_omega hω
  have hu : u ^ (2 ^ i) = u ^ (2 ^ eps) := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
    change ω ^ (2 ^ i) = ω ^ (2 ^ eps)
    exact hpowEq
  have hmod := (pow_eq_pow_iff_modEq (x := u)).mp hu
  have hmod3 : 2 ^ i % 3 = 2 ^ eps % 3 := by
    simpa [Nat.ModEq, huorder] using hmod
  have hparity : i % 2 = eps := parity_of_two_pow_mod_three heps hmod3
  have hδ2 : dualAut 3 K * dualAut 3 K = 1 := by
    obtain ⟨-, -, -, hdd, -, -⟩ := standard_automorphism_transport (K := K) (n := 3)
    exact hdd
  have hcomm : Commute (fieldAut 3 K φ) (dualAut 3 K) :=
    standardFieldGraph_commute (fieldAut_mem_standardFieldGraph φ)
      dualAut_mem_standardFieldGraph
  have hfi : (fieldAut 3 K φ) ^ i = fieldAut 3 K σ := by
    rw [← map_pow, hi]
  have hδpow : (dualAut 3 K) ^ i = (dualAut 3 K) ^ eps := by
    rw [dualAut_pow_eq_mod_two i, hparity]
  have hhi : (fieldAut 3 K φ * dualAut 3 K) ^ i =
      fieldAut 3 K σ * dualAut 3 K ^ eps := by
    rw [Commute.mul_pow hcomm i, hfi, hδpow]
  rw [← hhi]
  exact Subgroup.mem_zpowers_iff.mpr ⟨(i : ℤ), by rw [zpow_natCast]⟩

theorem mem_zpowers_pow_oddPart_of_pow_two_eq_one [Finite K] [CharP K 2]
    {n a m' : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : n = 2 ^ a * m') (hm : Odd m') {k : ℕ}
    {t : MulAut (projectiveSL 3 K)}
    (ht : t ∈ Subgroup.zpowers (fieldAut 3 K (frobeniusAut 2 K) * dualAut 3 K))
    (htk : t ^ (2 ^ k) = 1) :
    t ∈ Subgroup.zpowers ((fieldAut 3 K (frobeniusAut 2 K) * dualAut 3 K) ^ m') := by
  have htwo := frobenius_mul_dualAut_pow_two_mul (K := K) n hK
  have htwo' : (fieldAut 3 K (frobeniusAut 2 K) * dualAut 3 K) ^
      (2 * (2 ^ a * m')) = 1 := by
    simpa [hn] using htwo
  exact mem_zpowers_pow_of_pow_eq_one _ _ hm htwo' ht htk

theorem pow_oddPart_eq_fieldAut_mul_dualAut [Finite K] [CharP K 2] {m' : ℕ} (hm : Odd m') :
    (fieldAut 3 K (frobeniusAut 2 K) * dualAut 3 K) ^ m' =
      fieldAut 3 K ((frobeniusAut 2 K) ^ m') * dualAut 3 K := by
  let φ : K ≃+* K := frobeniusAut 2 K
  have hδ2 : dualAut 3 K * dualAut 3 K = 1 := by
    obtain ⟨-, -, -, hdd, -, -⟩ := standard_automorphism_transport (K := K) (n := 3)
    exact hdd
  have hcomm : Commute (fieldAut 3 K φ) (dualAut 3 K) :=
    standardFieldGraph_commute (fieldAut_mem_standardFieldGraph φ)
      dualAut_mem_standardFieldGraph
  rw [Commute.mul_pow hcomm m']
  have hfi : (fieldAut 3 K φ) ^ m' = fieldAut 3 K (φ ^ m') := by rw [← map_pow]
  have hδm : (dualAut 3 K) ^ m' = dualAut 3 K := by
    obtain ⟨t, ht⟩ := hm
    rw [ht, pow_succ, pow_mul, pow_two, hδ2, one_pow, one_mul]
  rw [hfi, hδm]

end CFSG.RankThree.PartTwo.KFacts.PSLThreeGraphField

end
