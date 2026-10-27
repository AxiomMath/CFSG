module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.Quasithin.A312U3

open Matrix
open scoped MatrixGroups

section TwoByTwo

variable {F : Type*} [Field F]

theorem fin_two_mul_self' (M : Matrix (Fin 2) (Fin 2) F) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem trace_eq_zero_of_anticomm {A B : Matrix (Fin 2) (Fin 2) F}
    (hA : ∀ s : F, A ≠ s • 1)
    (h : B * A + A * B = A.trace • B) : B.trace = 0 := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : F, A = !![a, b; c, d] := ⟨_, _, _, _, A.eta_fin_two⟩
  obtain ⟨x, y, z, w, rfl⟩ : ∃ x y z w : F, B = !![x, y; z, w] := ⟨_, _, _, _, B.eta_fin_two⟩
  have e12 := congrFun (congrFun h 0) 1
  have e21 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 0) 0
  have e22 := congrFun (congrFun h 1) 1
  simp [Matrix.trace_fin_two] at e12 e21 e11 e22
  have htr : (!![x, y; z, w] : Matrix (Fin 2) (Fin 2) F).trace = x + w := by
    simp [Matrix.trace_fin_two]
  rw [htr]
  have hb : b * (x + w) = 0 := by linear_combination e12
  have hc : c * (x + w) = 0 := by linear_combination e21
  have had : (a - d) * (x + w) = 0 := by linear_combination e11 - e22
  by_contra hne
  have hb0 : b = 0 := by
    rcases mul_eq_zero.mp hb with h | h
    · exact h
    · exact absurd h hne
  have hc0 : c = 0 := by
    rcases mul_eq_zero.mp hc with h | h
    · exact h
    · exact absurd h hne
  have had0 : a - d = 0 := by
    rcases mul_eq_zero.mp had with h | h
    · exact h
    · exact absurd h hne
  apply hA a
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hb0, hc0, sub_eq_zero.mp had0]

theorem trace_eq_zero_of_inverts {A B : Matrix (Fin 2) (Fin 2) F}
    (hA : A.det ≠ 0) (hB : B.det ≠ 0) (hA2 : ∀ s : F, A * A ≠ s • (1 : Matrix (Fin 2) (Fin 2) F))
    {κ : F} (h : A * B * A = κ • B) : B.trace = 0 := by
  have ch := fin_two_mul_self' A
  have ht : A.trace ≠ 0 := by
    intro h0
    apply hA2 (-A.det)
    rw [ch, h0, zero_smul, zero_sub, neg_smul]
  have hAns : ∀ s : F, A ≠ s • (1 : Matrix (Fin 2) (Fin 2) F) := by
    intro s hs
    apply hA2 (s ^ 2)
    rw [hs, smul_mul_smul_comm, one_mul, sq]
  have e1 : (A.trace • (1 : Matrix (Fin 2) (Fin 2) F) - A) * A = A.det • 1 := by
    rw [sub_mul, smul_mul_assoc, one_mul, ch]
    abel
  have hstar : A.det • (B * A) = κ • ((A.trace • (1 : Matrix (Fin 2) (Fin 2) F) - A) * B) := by
    have h1 : (A.trace • (1 : Matrix (Fin 2) (Fin 2) F) - A) * (A * B * A) =
        κ • ((A.trace • (1 : Matrix (Fin 2) (Fin 2) F) - A) * B) := by
      rw [h, Matrix.mul_smul]
    rw [← h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1]
    simp
  have hκ : κ ^ 2 = A.det ^ 2 := by
    have hd := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, Fintype.card_fin] at hd
    have : κ ^ 2 * B.det = A.det ^ 2 * B.det := by rw [← hd]; ring
    exact mul_right_cancel₀ hB this
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hκ with hk | hk
  ·
    rw [hk] at hstar
    have h3 : B * A = (A.trace • (1 : Matrix (Fin 2) (Fin 2) F) - A) * B :=
      smul_right_injective _ hA hstar
    refine trace_eq_zero_of_anticomm hAns ?_
    rw [h3, sub_mul, smul_mul_assoc, one_mul]
    abel
  ·
    rw [hk, neg_smul, ← smul_neg] at hstar
    have h3 : B * A = -((A.trace • (1 : Matrix (Fin 2) (Fin 2) F) - A) * B) :=
      smul_right_injective _ hA hstar
    have h4 := congrArg Matrix.trace h3
    rw [sub_mul, smul_mul_assoc, one_mul, Matrix.trace_neg, Matrix.trace_sub, Matrix.trace_smul,
      Matrix.trace_mul_comm B A] at h4
    have h5 : A.trace * B.trace = 0 := by
      simp only [smul_eq_mul] at h4
      linear_combination h4
    exact (mul_eq_zero.mp h5).resolve_left ht

end TwoByTwo

section PGL

variable {F : Type*} [Field F]

theorem gl2_mem_center_iff (g : GL (Fin 2) F) :
    g ∈ Subgroup.center (GL (Fin 2) F) ↔
      ∃ c : F, (g : Matrix (Fin 2) (Fin 2) F) = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
  rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, hc]⟩

theorem gl2_sq_mem_center (I J : GL (Fin 2) F)
    (hI : I ^ 2 ∉ Subgroup.center (GL (Fin 2) F))
    (hJ : J * I * J⁻¹ * I ∈ Subgroup.center (GL (Fin 2) F)) :
    J ^ 2 ∈ Subgroup.center (GL (Fin 2) F) := by
  obtain ⟨z, hz⟩ : ∃ z : GL (Fin 2) F, z = J * I * J⁻¹ * I := ⟨_, rfl⟩
  have hzc : z ∈ Subgroup.center (GL (Fin 2) F) := hz ▸ hJ
  have hzcomm : ∀ g : GL (Fin 2) F, g * z = z * g := Subgroup.mem_center_iff.mp hzc
  have hIJI : I * J * I = z * J := by
    calc I * J * I = I * (J * I * J⁻¹ * I) * I⁻¹ * J := by group
      _ = I * z * I⁻¹ * J := by rw [← hz]
      _ = z * J := by rw [hzcomm I]; group
  obtain ⟨c, hc⟩ := (gl2_mem_center_iff z).mp hzc
  have hABA : (I : Matrix (Fin 2) (Fin 2) F) * (J : Matrix (Fin 2) (Fin 2) F) * I =
      c • (J : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hIJI
    simp only [Units.val_mul, hc, smul_mul_assoc, one_mul] at this
    exact this
  have hdI : (I : Matrix (Fin 2) (Fin 2) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp I.isUnit).ne_zero
  have hdJ : (J : Matrix (Fin 2) (Fin 2) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp J.isUnit).ne_zero
  have hI2 : ∀ s : F, (I : Matrix (Fin 2) (Fin 2) F) * I ≠ s • (1 : Matrix (Fin 2) (Fin 2) F) := by
    intro s hs
    apply hI
    rw [gl2_mem_center_iff]
    exact ⟨s, by rw [pow_two, Units.val_mul, hs]⟩
  have htr := trace_eq_zero_of_inverts hdI hdJ hI2 hABA
  rw [gl2_mem_center_iff]
  refine ⟨-(J : Matrix (Fin 2) (Fin 2) F).det, ?_⟩
  rw [pow_two, Units.val_mul, fin_two_mul_self', htr, zero_smul, zero_sub, neg_smul]

end PGL

end CFSG.Quasithin.A312U3
