module

public import CFSG.Quasithin.H13.GoldschmidtU43EMat5

public section

namespace CFSG.Quasithin.H13.U43

@[expose] def Amat1 : Mat3 := !![1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0]
@[expose] def Amat2 : Mat3 := !![1, 0, 0, 0; 0, 0, 0, 1; 0, 2, 0, 0; 0, 0, 2, 0]
@[expose] def Amat3 : Mat3 := !![1, 0, 0, 0; 0, 0, 0, 2; 0, 1, 0, 0; 0, 0, 2, 0]
@[expose] def Amat4 : Mat3 := !![1, 0, 0, 0; 0, 0, 0, 2; 0, 2, 0, 0; 0, 0, 1, 0]

@[expose] def Bmat1 : Mat3 := !![0, 0, 2, 1; 0, 1, 0, 0; 1, 0, 2, 2; 1, 0, 1, 1]
@[expose] def Bmat2 : Mat3 := !![0, 0, 2, 1; 0, 1, 0, 0; 2, 0, 1, 1; 2, 0, 2, 2]
@[expose] def Bmat3 : Mat3 := !![0, 0, 1, 2; 0, 1, 0, 0; 1, 0, 1, 1; 1, 0, 2, 2]
@[expose] def Bmat4 : Mat3 := !![0, 0, 1, 2; 0, 1, 0, 0; 2, 0, 2, 2; 2, 0, 1, 1]

theorem Bmat1_eq : Bmat1 = Pinv * Amat1 * Pmat := by decide
theorem Bmat2_eq : Bmat2 = Pinv * Amat2 * Pmat := by decide
theorem Bmat3_eq : Bmat3 = Pinv * Amat3 * Pmat := by decide
theorem Bmat4_eq : Bmat4 = Pinv * Amat4 * Pmat := by decide

theorem shapeA_cube (a d f g : ZMod 3) :
    (!![a, 0, 0, 0; 0, 0, 0, d; 0, f, 0, 0; 0, 0, g, 0] : Mat3) ^ 3 =
      Matrix.diagonal ![a * a * a, d * f * g, d * f * g, d * f * g] := by
  rw [pow_three']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal] <;> first | (left; ring) | ring

theorem A_cases {X : Mat3} (h1 : X * Zmat = Umat * X) (h2 : X * Umat = (Zmat * Umat) * X)
    (h3 : X ^ 3 = 1) : X = Amat1 ∨ X = Amat2 ∨ X = Amat3 ∨ X = Amat4 := by
  have hs := shape_A h1 h2
  rw [hs, shapeA_cube] at h3
  have hd : Matrix.diagonal ![X 0 0 * X 0 0 * X 0 0, X 1 3 * X 2 1 * X 3 2, X 1 3 * X 2 1 * X 3 2,
      X 1 3 * X 2 1 * X 3 2] = (1 : Mat3) := h3
  have e0 := congrFun (congrFun hd 0) 0
  have e1 := congrFun (congrFun hd 1) 1
  simp [Matrix.diagonal] at e0 e1
  have key : ∀ a d f g : ZMod 3, a * a * a = 1 → d * f * g = 1 →
      (a = 1 ∧ d = 1 ∧ f = 1 ∧ g = 1) ∨ (a = 1 ∧ d = 1 ∧ f = 2 ∧ g = 2) ∨
      (a = 1 ∧ d = 2 ∧ f = 1 ∧ g = 2) ∨ (a = 1 ∧ d = 2 ∧ f = 2 ∧ g = 1) := by decide
  rcases key _ _ _ _ e0 e1 with ⟨ha, hd', hf, hg⟩ | ⟨ha, hd', hf, hg⟩ | ⟨ha, hd', hf, hg⟩ |
      ⟨ha, hd', hf, hg⟩
  · left; rw [hs, ha, hd', hf, hg]; rfl
  · right; left; rw [hs, ha, hd', hf, hg]; rfl
  · right; right; left; rw [hs, ha, hd', hf, hg]; rfl
  · right; right; right; rw [hs, ha, hd', hf, hg]; rfl

theorem conj_pow_three {P Q Y : Mat3} (hQP : Q * P = 1) :
    (P * Y * Q) ^ 3 = P * Y ^ 3 * Q := by
  rw [pow_three', pow_three']
  calc P * Y * Q * (P * Y * Q) * (P * Y * Q)
      = P * Y * (Q * P) * Y * (Q * P) * Y * Q := by simp only [Matrix.mul_assoc]
    _ = P * (Y * Y * Y) * Q := by rw [hQP]; simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem B_cases {Y : Mat3} (h1 : Y * Zmat = Wmat * Y) (h2 : Y * Wmat = (Zmat * Wmat) * Y)
    (h3 : Y ^ 3 = 1) : Y = Bmat1 ∨ Y = Bmat2 ∨ Y = Bmat3 ∨ Y = Bmat4 := by
  obtain ⟨c1, c2⟩ := conj_shape h1 h2
  have h3' : (Pmat * Y * Pinv) ^ 3 = 1 := by
    rw [conj_pow_three Pinv_Pmat, h3, Matrix.mul_one, Pmat_Pinv]
  have hY : Y = Pinv * (Pmat * Y * Pinv) * Pmat := by
    calc Y = (Pinv * Pmat) * Y * (Pinv * Pmat) := by rw [Pinv_Pmat, Matrix.one_mul, Matrix.mul_one]
      _ = Pinv * (Pmat * Y * Pinv) * Pmat := by simp only [Matrix.mul_assoc]
  rcases A_cases c1 c2 h3' with h | h | h | h
  · left; rw [hY, h, Bmat1_eq]
  · right; left; rw [hY, h, Bmat2_eq]
  · right; right; left; rw [hY, h, Bmat3_eq]
  · right; right; right; rw [hY, h, Bmat4_eq]

end CFSG.Quasithin.H13.U43
