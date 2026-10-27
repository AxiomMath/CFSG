module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.L3Lin

open Matrix

variable {F : Type} [Field F]

theorem cube_eq_one_of_mul_eq_smul {G X : Matrix (Fin 3) (Fin 3) F} (hG : G.det ≠ 0)
    (hX : X.det ≠ 0) {ν : F} (h : G * X = ν • (X * G)) : ν ^ 3 = 1 := by
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_mul, Fintype.card_fin] at hd
  have : G.det * X.det * (ν ^ 3 - 1) = 0 := by linear_combination -hd
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (mul_ne_zero hG hX))

theorem entries_of_comm_block {G : Matrix (Fin 3) (Fin 3) F} (hG : G.det ≠ 0)
    {b00 b01 b10 b11 u : F} (hdet : b00 * b11 - b01 * b10 = 1) (ht2 : b00 + b11 ≠ 2)
    (ht1 : b00 + b11 ≠ -1)
    (h : G * !![b00, b01, 0; b10, b11, 0; 0, 0, 1] =
      u • (!![b00, b01, 0; b10, b11, 0; 0, 0, 1] * G)) :
    G 0 2 = 0 ∧ G 1 2 = 0 ∧ G 2 0 = 0 ∧ G 2 1 = 0 := by
  have hX : (!![b00, b01, 0; b10, b11, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
    have hd : (!![b00, b01, 0; b10, b11, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F).det =
        b00 * b11 - b01 * b10 := by
      simp [Matrix.det_fin_three]
    rw [hd, hdet]
    exact one_ne_zero
  have hu3 : u ^ 3 = 1 := cube_eq_one_of_mul_eq_smul hG hX h
  have e := fun i j => congrFun (congrFun h i) j
  have e00 := e 0 0; have e01 := e 0 1; have e02 := e 0 2
  have e10 := e 1 0; have e11 := e 1 1; have e12 := e 1 2
  have e20 := e 2 0; have e21 := e 2 1; have e22 := e 2 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct]
    at e00 e01 e02 e10 e11 e12 e20 e21 e22
  rw [Matrix.det_fin_three] at hG
  by_cases h22 : G 2 2 = 0
  · exfalso
    grind
  · have hu : u = 1 := by grind
    subst hu
    refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

theorem entries_of_comm_diag {G : Matrix (Fin 3) (Fin 3) F} (hG : G.det ≠ 0) {a u : F}
    (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (h : G * !![a, 0, 0; 0, a, 0; 0, 0, 1] = u • (!![a, 0, 0; 0, a, 0; 0, 0, 1] * G)) :
    G 0 2 = 0 ∧ G 1 2 = 0 ∧ G 2 0 = 0 ∧ G 2 1 = 0 := by
  have e := fun i j => congrFun (congrFun h i) j
  have e00 := e 0 0; have e01 := e 0 1; have e02 := e 0 2
  have e10 := e 1 0; have e11 := e 1 1; have e12 := e 1 2
  have e20 := e 2 0; have e21 := e 2 1; have e22 := e 2 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct]
    at e00 e01 e02 e10 e11 e12 e20 e21 e22
  rw [Matrix.det_fin_three] at hG
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

theorem false_of_conj_diag_inv {G : Matrix (Fin 3) (Fin 3) F} (hG : G.det ≠ 0) {a b u : F}
    (hab : a * b = 1) (ha2 : a * a ≠ 1)
    (h : G * !![a, 0, 0; 0, a, 0; 0, 0, 1] = u • (!![b, 0, 0; 0, b, 0; 0, 0, 1] * G)) :
    False := by
  have e := fun i j => congrFun (congrFun h i) j
  have e00 := e 0 0; have e01 := e 0 1; have e02 := e 0 2
  have e10 := e 1 0; have e11 := e 1 1; have e12 := e 1 2
  have e20 := e 2 0; have e21 := e 2 1; have e22 := e 2 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct]
    at e00 e01 e02 e10 e11 e12 e20 e21 e22
  rw [Matrix.det_fin_three] at hG
  grind

theorem shape_of_inv_comm (h2 : (2 : F) ≠ 0) {G : Matrix (Fin 3) (Fin 3) F} {μ ν : F}
    (hr : G * !![1, 0, 0; 0, -1, 0; 0, 0, -1] = !![1, 0, 0; 0, -1, 0; 0, 0, -1] * G)
    (hz : !![-1, 0, 0; 0, -1, 0; 0, 0, 1] * G * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] * G = μ • 1)
    (he : G * (!![0, -1, 0; 1, 0, 0; 0, 0, 1] * G * !![0, 1, 0; -1, 0, 0; 0, 0, 1]) =
      ν • ((!![0, -1, 0; 1, 0, 0; 0, 0, 1] * G * !![0, 1, 0; -1, 0, 0; 0, 0, 1]) * G)) :
    (∃ s : F, G * G = s • 1) ∨ (G 0 1 = 0 ∧ G 0 2 = 0 ∧ G 1 0 = 0 ∧ G 2 0 = 0 ∧
      G 1 1 = G 0 0 ∧ G 2 2 = G 0 0 ∧ G 1 2 * G 2 1 = 0) := by
  have r := fun i j => congrFun (congrFun hr i) j
  have r01 := r 0 1; have r02 := r 0 2; have r10 := r 1 0; have r20 := r 2 0
  simp [Matrix.mul_apply, Fin.sum_univ_three] at r01 r02 r10 r20
  have h01 : G 0 1 = 0 := by grind
  have h02 : G 0 2 = 0 := by grind
  have h10 : G 1 0 = 0 := by grind
  have h20 : G 2 0 = 0 := by grind
  have z := fun i j => congrFun (congrFun hz i) j
  have z00 := z 0 0; have z11 := z 1 1; have z12 := z 1 2; have z21 := z 2 1; have z22 := z 2 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct, h01, h02, h10, h20]
    at z00 z11 z12 z21 z22
  have w := fun i j => congrFun (congrFun he i) j
  have w00 := w 0 0; have w01 := w 0 1; have w02 := w 0 2; have w10 := w 1 0
  have w12 := w 1 2; have w20 := w 2 0; have w21 := w 2 1; have w22 := w 2 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct, h01, h02, h10, h20]
    at w00 w01 w02 w10 w12 w20 w21 w22
  by_cases hbc : G 1 2 = 0 ∧ G 2 1 = 0
  · left
    refine ⟨G 0 0 * G 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, h01, h02, h10, h20, hbc.1, hbc.2] <;> grind
  · right
    refine ⟨h01, h02, h10, h20, ?_, ?_, ?_⟩ <;> grind

theorem eq_scalar_of_comm_unip (h3 : (3 : F) ≠ 0) {G : Matrix (Fin 3) (Fin 3) F}
    (hG : G.det ≠ 0) {x β γ s : F} (hβγ : β * γ = 0) (hne : β ≠ 0 ∨ γ ≠ 0)
    (h1 : G * !![x, 0, 0; 0, x, β; 0, γ, x] = !![x, 0, 0; 0, x, β; 0, γ, x] * G)
    (h2 : G * !![x, 0, -β; 0, x, 0; -γ, 0, x] = !![x, 0, -β; 0, x, 0; -γ, 0, x] * G)
    (hs : G * G * G = s • 1) : ∃ c : F, G = c • 1 := by
  have a := fun i j => congrFun (congrFun h1 i) j
  have b := fun i j => congrFun (congrFun h2 i) j
  have a00 := a 0 0; have a01 := a 0 1; have a02 := a 0 2
  have a10 := a 1 0; have a11 := a 1 1; have a12 := a 1 2
  have a20 := a 2 0; have a21 := a 2 1; have a22 := a 2 2
  have b00 := b 0 0; have b01 := b 0 1; have b02 := b 0 2
  have b10 := b 1 0; have b11 := b 1 1; have b12 := b 1 2
  have b20 := b 2 0; have b21 := b 2 1; have b22 := b 2 2
  simp [Matrix.mul_apply, Fin.sum_univ_three]
    at a00 a01 a02 a10 a11 a12 a20 a21 a22 b00 b01 b02 b10 b11 b12 b20 b21 b22
  rcases hne with hβ | hγ
  · have hγ : γ = 0 := by grind
    subst hγ
    have g01 : G 0 1 = 0 := by grind
    have g10 : G 1 0 = 0 := by grind
    have g20 : G 2 0 = 0 := by grind
    have g21 : G 2 1 = 0 := by grind
    have g11 : G 1 1 = G 0 0 := by grind
    have g22 : G 2 2 = G 0 0 := by grind
    have c := fun i j => congrFun (congrFun hs i) j
    have c02 := c 0 2; have c12 := c 1 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, g01, g10, g20, g21, g11, g22] at c02 c12
    rw [Matrix.det_fin_three, g01, g10, g20, g21, g11, g22] at hG
    have g02 : G 0 2 = 0 := by grind
    have g12 : G 1 2 = 0 := by grind
    refine ⟨G 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [g01, g10, g20, g21, g11, g22, g02, g12]
  · have hβ : β = 0 := by grind
    subst hβ
    have g01 : G 0 1 = 0 := by grind
    have g10 : G 1 0 = 0 := by grind
    have g02 : G 0 2 = 0 := by grind
    have g12 : G 1 2 = 0 := by grind
    have g11 : G 1 1 = G 0 0 := by grind
    have g22 : G 2 2 = G 0 0 := by grind
    have c := fun i j => congrFun (congrFun hs i) j
    have c20 := c 2 0; have c21 := c 2 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, g01, g10, g02, g12, g11, g22] at c20 c21
    rw [Matrix.det_fin_three, g01, g10, g02, g12, g11, g22] at hG
    have g20 : G 2 0 = 0 := by grind
    have g21 : G 2 1 = 0 := by grind
    refine ⟨G 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [g01, g10, g20, g21, g11, g22, g02, g12]

theorem sl2_mul_self (B : Matrix (Fin 2) (Fin 2) F) (hB : B.det = 1) :
    B * B = B.trace • B - 1 := by
  rw [Matrix.det_fin_two] at hB
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;> grind

theorem pow_char_eq_one_of_trace {p : ℕ} [hp : Fact p.Prime] [CharP F p]
    (B : Matrix (Fin 2) (Fin 2) F) (hB : B.det = 1) (ht : B.trace = 2) : B ^ p = 1 := by
  have hN : (B - 1) * (B - 1) = 0 := by
    have h := sl2_mul_self B hB
    rw [ht] at h
    rw [sub_mul, mul_sub, mul_sub, h, mul_one, one_mul, one_mul]
    rw [two_smul]
    abel
  have hcomm : Commute (1 : Matrix (Fin 2) (Fin 2) F) (B - 1) := Commute.one_left _
  have hp2 : 2 ≤ p := hp.out.two_le
  have hNp : (B - 1) ^ p = 0 := by
    obtain ⟨k, hk⟩ : ∃ k, p = k + 2 := ⟨p - 2, by omega⟩
    rw [hk, pow_add, sq, hN, mul_zero]
  calc B ^ p = (1 + (B - 1)) ^ p := by rw [add_sub_cancel]
    _ = 1 := by rw [add_pow_char_of_commute p hcomm, one_pow, hNp, add_zero]

theorem pow_three_eq_one_of_trace (B : Matrix (Fin 2) (Fin 2) F) (hB : B.det = 1)
    (ht : B.trace = -1) : B ^ 3 = 1 := by
  have h := sl2_mul_self B hB
  rw [ht, neg_one_smul] at h
  calc B ^ 3 = B * (B * B) := by rw [pow_three]
    _ = 1 := by
      rw [h, mul_sub, mul_neg, h, mul_one]
      abel
end CFSG.LocalAnalysis.UniquenessCase.UC22.L3Lin
