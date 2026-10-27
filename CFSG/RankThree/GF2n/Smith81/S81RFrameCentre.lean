module

public import CFSG.RankThree.GF2n.Smith81.S81A5Cent

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix

variable {K : Type*} [Field K]

private theorem frame_dual_pair {f g : Fin 6 → K} (hfg : LinearIndependent K ![f, g]) :
    ∃ p₁ p₂ : Fin 6 → K, f ⬝ᵥ p₁ = 1 ∧ g ⬝ᵥ p₁ = 0 ∧ f ⬝ᵥ p₂ = 0 ∧ g ⬝ᵥ p₂ = 1 := by
  rw [LinearIndependent.pair_iff] at hfg
  obtain ⟨i, k, hD⟩ : ∃ i k : Fin 6, f i * g k - f k * g i ≠ 0 := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin 6, f i₀ ≠ 0 := by
      by_contra hf
      simp only [not_exists, ne_eq, not_not] at hf
      have hf0 : f = 0 := funext hf
      exact one_ne_zero (hfg 1 0 (by simp [hf0])).1
    have hdep := hfg (g i₀ / f i₀) (-1) (by
      funext j
      have key : g j = g i₀ / f i₀ * f j := by
        rw [div_mul_eq_mul_div, eq_div_iff hi₀]
        linear_combination hcon i₀ j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [key]
      ring)
    exact (neg_ne_zero.mpr one_ne_zero) hdep.2
  refine ⟨(g k / (f i * g k - f k * g i)) • e K i + (-(g i / (f i * g k - f k * g i))) • e K k,
    (-(f k / (f i * g k - f k * g i))) • e K i + (f i / (f i * g k - f k * g i)) • e K k,
    ?_, ?_, ?_, ?_⟩
  · simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, e, dotProduct_single, mul_one]
    linear_combination (mul_inv_cancel₀ hD)
  · simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, e, dotProduct_single, mul_one]
    ring
  · simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, e, dotProduct_single, mul_one]
    ring
  · simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, e, dotProduct_single, mul_one]
    linear_combination (mul_inv_cancel₀ hD)

private theorem frame_unip_det (u w : Fin 6 → K) (hu0 : u 0 = 0) (hu1 : u 1 = 0) (hw0 : w 0 = 0)
    (hw1 : w 1 = 0) (hw2 : w 2 = 0) :
    (1 + vecMulVec (e K 1) u + vecMulVec (e K 2) w : Matrix (Fin 6) (Fin 6) K).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [Fin.prod_univ_six, Matrix.one_apply, Matrix.vecMulVec, e, Pi.single_apply, hu0, hu1,
      hw0, hw1, hw2]
  · intro i j hji
    revert hji
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.one_apply, Matrix.vecMulVec, e, Pi.single_apply, hu0, hu1, hw0, hw1, hw2]

private theorem frame_Q {φ ψ : Fin 6 → K} (hφ0 : φ 0 = 0) (hφ1 : φ 1 = 1) (hφ2 : φ 2 = 0)
    (hψ0 : ψ 0 = 0) (hψ1 : ψ 1 = 0) (hψ2 : ψ 2 = 1) :
    ∃ Q : Matrix (Fin 6) (Fin 6) K, Q.det = 1 ∧ φ ᵥ* Q = e K 1 ∧ ψ ᵥ* Q = e K 2 ∧
      Q *ᵥ e K 0 = e K 0 := by
  obtain ⟨u, hu⟩ : ∃ u : Fin 6 → K, u = fun j => if 2 < j.val then -φ j else 0 := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Fin 6 → K, w = fun j => if 2 < j.val then -ψ j else 0 := ⟨_, rfl⟩
  have hu0 : u 0 = 0 := by simp [hu]
  have hu1 : u 1 = 0 := by simp [hu]
  have hw0 : w 0 = 0 := by simp [hw]
  have hw1 : w 1 = 0 := by simp [hw]
  have hw2 : w 2 = 0 := by simp [hw]
  refine ⟨1 + vecMulVec (e K 1) u + vecMulVec (e K 2) w, frame_unip_det u w hu0 hu1 hw0 hw1 hw2,
    ?_, ?_, ?_⟩
  · rw [Matrix.vecMul_add, Matrix.vecMul_add, Matrix.vecMul_one, Matrix.vecMul_vecMulVec,
      Matrix.vecMul_vecMulVec]
    funext j
    fin_cases j <;> simp [e, hu, hφ0, hφ1, hφ2]
  · rw [Matrix.vecMul_add, Matrix.vecMul_add, Matrix.vecMul_one, Matrix.vecMul_vecMulVec,
      Matrix.vecMul_vecMulVec]
    funext j
    fin_cases j <;> simp [e, hw, hψ0, hψ1, hψ2]
  · rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, fe3_vecMulVec_mulVec,
      fe3_vecMulVec_mulVec]
    simp [e, hu0, hw0]

theorem exists_frame_centre {a f g : Fin 6 → K} (ha : a ≠ 0) (hfa : f ⬝ᵥ a = 0)
    (hga : g ⬝ᵥ a = 0) (hfg : LinearIndependent K ![f, g]) :
    ∃ (c : Matrix (Fin 6) (Fin 6) K) (α β : K), c.det = 1 ∧ α ≠ 0 ∧ β ≠ 0 ∧ c *ᵥ a = e K 0 ∧
      f ᵥ* c⁻¹ = α • e K 1 ∧ g ᵥ* c⁻¹ = β • e K 2 := by
  obtain ⟨p₁, p₂, hp₁f, hp₁g, hp₂f, hp₂g⟩ := frame_dual_pair hfg
  have hind : LinearIndependent K ![a, p₁, p₂] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc' : c 0 • a + c 1 • p₁ + c 2 • p₂ = 0 := by simpa [Fin.sum_univ_three] using hc
    have h1 : c 1 = 0 := by
      have h := congrArg (fun x => f ⬝ᵥ x) hc'
      simpa [dotProduct_add, dotProduct_smul, hfa, hp₁f, hp₂f] using h
    have h2 : c 2 = 0 := by
      have h := congrArg (fun x => g ⬝ᵥ x) hc'
      simpa [dotProduct_add, dotProduct_smul, hga, hp₁g, hp₂g] using h
    have h0 : c 0 = 0 := by
      have h : c 0 • a = 0 := by simpa [h1, h2] using hc'
      exact (smul_eq_zero.mp h).resolve_right ha
    intro i
    fin_cases i <;> simp [h0, h1, h2]
  have hE : LinearIndependent K ![e K 0, e K 1, e K 2] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc' : c 0 • e K 0 + c 1 • e K 1 + c 2 • e K 2 = 0 := by
      simpa [Fin.sum_univ_three] using hc
    have h0 := congrFun hc' 0
    have h1 := congrFun hc' 1
    have h2 := congrFun hc' 2
    simp [e, Pi.single_apply] at h0 h1 h2
    intro i
    fin_cases i <;> simp [h0, h1, h2]
  obtain ⟨P₃, hP₃det, hP₃⟩ :=
    exists_sl_of_linearIndependent (by norm_num : (3 : ℕ) < 6) hE hind
  have hP₃0 : P₃ *ᵥ e K 0 = a := hP₃ 0
  have hP₃1 : P₃ *ᵥ e K 1 = p₁ := hP₃ 1
  have hP₃2 : P₃ *ᵥ e K 2 = p₂ := hP₃ 2
  have hφ0 : (f ᵥ* P₃) 0 = 0 := by rw [fe3_vecMul_apply_e, hP₃0, hfa]
  have hφ1 : (f ᵥ* P₃) 1 = 1 := by rw [fe3_vecMul_apply_e, hP₃1, hp₁f]
  have hφ2 : (f ᵥ* P₃) 2 = 0 := by rw [fe3_vecMul_apply_e, hP₃2, hp₂f]
  have hψ0 : (g ᵥ* P₃) 0 = 0 := by rw [fe3_vecMul_apply_e, hP₃0, hga]
  have hψ1 : (g ᵥ* P₃) 1 = 0 := by rw [fe3_vecMul_apply_e, hP₃1, hp₁g]
  have hψ2 : (g ᵥ* P₃) 2 = 1 := by rw [fe3_vecMul_apply_e, hP₃2, hp₂g]
  obtain ⟨Q, hQdet, hφQ, hψQ, hQ0⟩ := frame_Q hφ0 hφ1 hφ2 hψ0 hψ1 hψ2
  obtain ⟨P, hPdef⟩ : ∃ P : Matrix (Fin 6) (Fin 6) K, P = P₃ * Q := ⟨_, rfl⟩
  have hPdet : P.det = 1 := by rw [hPdef, Matrix.det_mul, hP₃det, hQdet, one_mul]
  have hPu : IsUnit P.det := by rw [hPdet]; exact isUnit_one
  have hPe0 : P *ᵥ e K 0 = a := by rw [hPdef, ← Matrix.mulVec_mulVec, hQ0, hP₃0]
  refine ⟨P⁻¹, 1, 1, ?_, one_ne_zero, one_ne_zero, ?_, ?_, ?_⟩
  · simp [Matrix.det_nonsing_inv, hPdet]
  · rw [← hPe0, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P hPu, Matrix.one_mulVec]
  · rw [Matrix.nonsing_inv_nonsing_inv P hPu, one_smul, hPdef, ← Matrix.vecMul_vecMul, hφQ]
  · rw [Matrix.nonsing_inv_nonsing_inv P hPu, one_smul, hPdef, ← Matrix.vecMul_vecMul, hψQ]

end CFSG.RankThree.GF2n.Smith81.A5Cube
