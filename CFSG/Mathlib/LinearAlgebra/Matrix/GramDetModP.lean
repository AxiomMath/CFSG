module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.MatrixDet

private theorem det_one_updateRow {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]
    (j : ι) (c : ι → R) : ((1 : Matrix ι ι R).updateRow j c).det = c j := by
  have hrow : (∑ i, (c i) • (1 : Matrix ι ι R) i) = c := by
    funext l
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.one_apply]
    rw [Fintype.sum_eq_single l (fun x hx => by simp [hx])]
    simp
  have h : (1 : Matrix ι ι R).updateRow j c
      = (1 : Matrix ι ι R).updateRow j (∑ i, (c i) • (1 : Matrix ι ι R) i) := by
    rw [hrow]
  rw [h, Matrix.det_updateRow_sum (1 : Matrix ι ι R) j c, Matrix.det_one]
  simp

theorem linearIndependent_zmod_of_not_sq_dvd_det_gram {k n : Type*} [Fintype k] [DecidableEq k]
    [Fintype n] {p : ℕ} [Fact p.Prime] (B : Matrix n n ℤ) (v : Matrix k n ℤ)
    (h : ¬ (p : ℤ) ^ 2 ∣ (v * B * v.transpose).det) :
    LinearIndependent (ZMod p) fun i => (v.map (Int.cast : ℤ → ZMod p)) i := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set w : k → n → ZMod p := fun i => (v.map (Int.cast : ℤ → ZMod p)) i with hw
  by_contra hli
  obtain ⟨g, hg, j, hgj⟩ := Fintype.not_linearIndependent_iff.mp hli
  let g' : k → ZMod p := (g j)⁻¹ • g
  have hg'j : g' j = 1 := by
    change (g j)⁻¹ * g j = 1
    exact inv_mul_cancel₀ hgj
  have hg'sum : ∑ i, g' i • w i = 0 := by
    have hterm : ∀ i, g' i • w i = (g j)⁻¹ • (g i • w i) := by
      intro i
      change ((g j)⁻¹ * g i) • w i = (g j)⁻¹ • (g i • w i)
      rw [mul_smul]
    simp_rw [hterm]
    rw [← Finset.smul_sum, hg, smul_zero]
  let c : k → ℤ := fun i => ((g' i).val : ℤ)
  have hc : ∀ i, (c i : ZMod p) = g' i := by
    intro i
    have h1 : (c i : ZMod p) = ((g' i).val : ZMod p) := by
      simp only [c, Int.cast_natCast]
    rw [h1, ZMod.natCast_zmod_val]
  have hc_j : c j = 1 := by
    have h1 : c j = (((g' j).val : ℕ) : ℤ) := rfl
    have h2 : (g' j).val = 1 := by
      rw [hg'j]
      have h3 : (1 : ZMod p) = ((1 : ℕ) : ZMod p) := Nat.cast_one.symm
      rw [h3]
      exact ZMod.val_natCast_of_lt (Fact.out : p.Prime).one_lt
    rw [h1, h2]
    norm_num
  let E : Matrix k k ℤ := (1 : Matrix k k ℤ).updateRow j c
  have hE : E.det = 1 := by
    change ((1 : Matrix k k ℤ).updateRow j c).det = 1
    rw [det_one_updateRow j c, hc_j]
  let W : Matrix k n ℤ := E * v
  have hWrow : W j = ∑ i, (c i) • v i := by
    funext l
    simp only [W, E, Matrix.mul_apply, Matrix.updateRow_self, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
  have hWmod : ∀ l, ((W j l : ℤ) : ZMod p) = 0 := by
    intro l
    have hcast : ((W j l : ℤ) : ZMod p) = (∑ i, g' i • w i) l := by
      rw [hWrow]
      rw [Finset.sum_apply, Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      push_cast
      apply Finset.sum_congr rfl
      intro i _
      rw [hc i]
      rfl
    rw [hcast, hg'sum, Pi.zero_apply]
  choose u hu using fun l => (ZMod.intCast_zmod_eq_zero_iff_dvd (W j l) p).mp (hWmod l)
  have hWu : W j = (p : ℤ) • u := by
    funext l
    rw [hu l, Pi.smul_apply, smul_eq_mul]
  let d : k → ℤ := fun i => if i = j then (p : ℤ) else 1
  let D : Matrix k k ℤ := Matrix.diagonal d
  have hDdet : D.det = (p : ℤ) := by
    change (Matrix.diagonal d).det = (p : ℤ)
    rw [Matrix.det_diagonal]
    rw [Fintype.prod_eq_single (f := d) j (fun x hx => by simp [d, hx])]
    simp [d]
  let W' : Matrix k n ℤ := W.updateRow j u
  have hWdecomp : W = D * W' := by
    funext i l
    change W i l = (Matrix.diagonal d * W') i l
    rw [Matrix.diagonal_mul]
    by_cases hi : i = j
    · rw [hi]
      have h1 : W' j l = u l := by simp only [W', Matrix.updateRow_self]
      rw [h1, hu l]
      simp [d]
    · have h1 : W' i l = W i l := by simp only [W', Matrix.updateRow_ne hi]
      rw [h1]
      simp [d, hi]
  have hDt : D.transpose = D := by
    rw [show D = Matrix.diagonal d from rfl, Matrix.diagonal_transpose]
  have hWt : W.transpose = W'.transpose * D := by
    rw [hWdecomp, Matrix.transpose_mul, hDt]
  have hWbWt : W * B * W.transpose = D * (W' * B * W'.transpose) * D := by
    rw [hWt, hWdecomp]
    simp only [Matrix.mul_assoc]
  have hdet1 : (W * B * W.transpose).det
      = (p : ℤ) ^ 2 * (W' * B * W'.transpose).det := by
    rw [hWbWt, Matrix.det_mul, Matrix.det_mul, hDdet]
    ring
  have hWv : W = E * v := rfl
  have hWtE : W.transpose = v.transpose * E.transpose := by
    rw [hWv, Matrix.transpose_mul]
  have hWbWtE : W * B * W.transpose = E * (v * B * v.transpose) * E.transpose := by
    rw [hWtE, hWv]
    simp only [Matrix.mul_assoc]
  have hdet2 : (W * B * W.transpose).det = (v * B * v.transpose).det := by
    rw [hWbWtE, Matrix.det_mul, Matrix.det_mul, hE, Matrix.det_transpose, hE]
    ring
  have hdvd : (p : ℤ) ^ 2 ∣ (v * B * v.transpose).det := by
    rw [← hdet2, hdet1]
    exact dvd_mul_right _ _
  exact h hdvd

end CFSG.MatrixDet
