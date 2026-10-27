module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.Quasithin.H13.L828SixLem

private lemma gl2t_two_eq_zero (K : Type) [Field K] [Finite K] (hK : Nat.card K = 4) :
    (2 : K) = 0 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have h4 : ((Fintype.card K : ℕ) : K) = 0 := FiniteField.cast_card_eq_zero K
  rw [hc] at h4
  have h4' : (4 : K) = 0 := by exact_mod_cast h4
  have h22 : (2 : K) * 2 = 0 := by linear_combination h4'
  rcases mul_eq_zero.mp h22 with h | h <;> exact h

private lemma gl2t_pow_four (K : Type) [Field K] [Finite K] (hK : Nat.card K = 4) (t : K) :
    t ^ 4 = t := by
  haveI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have h := FiniteField.pow_card t
  rw [hc] at h
  exact h

private lemma gl2t_cayley_hamilton {K : Type} [CommRing K] (g : Matrix (Fin 2) (Fin 2) K) :
    g * g = g.trace • g - g.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two,
      Matrix.one_apply] <;> ring

private lemma gl2t_scalar_det {K : Type} [Field K] (h2 : (2 : K) = 0) (a b c d : K)
    (e1 : 1 = a * b) (e2 : 1 = c * d) (e3 : c * a * d = b) : a = 1 := by
  have hab : b = a := by linear_combination -e3 - a * e2
  have haa : a * a = 1 := by linear_combination -e1 - a * hab
  have hsq : (a - 1) ^ 2 = 0 := by linear_combination haa + (1 - a) * h2
  exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq)

private lemma gl2t_trace_quad {K : Type} [Field K] (h2 : (2 : K) = 0)
    (G : Matrix (Fin 2) (Fin 2) K) (t : K) (ht4 : t ^ 4 = t) (hCH : G * G = t • G - 1)
    (hG5 : G ^ 5 = 1) (hG1 : G ≠ 1) : t ^ 2 + t + 1 = 0 := by
  have hm1 : (-1 : K) = 1 := by linear_combination -h2
  have hmulg : ∀ α β : K, G * (α • G + β • (1 : Matrix (Fin 2) (Fin 2) K))
      = (α * t + β) • G + (-α) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    intro α β
    rw [mul_add, mul_smul_comm, mul_smul_comm, mul_one, hCH]
    module
  have hp2 : G ^ 2 = t • G + (-1 : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [sq, hCH]
    module
  have hp3 : G ^ 3 = (t * t + -1) • G + (-t) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [show G ^ 3 = G * G ^ 2 from pow_succ' G 2, hp2, hmulg]
  have hsq1 : G ^ 2 = 1 → False := by
    intro h
    apply hG1
    calc G = (G ^ 2) ^ 2 * G := by rw [h, one_pow, one_mul]
      _ = G ^ 5 := by rw [← pow_mul, ← pow_succ] <;> rfl
      _ = 1 := hG5
  have hfac : t * ((t + 1) * (t ^ 2 + t + 1)) = 0 := by
    linear_combination ht4 + (t ^ 3 + t ^ 2 + t) * h2
  rcases mul_eq_zero.mp hfac with ht0 | hrest
  · exfalso
    apply hsq1
    rw [hp2, ht0, zero_smul, zero_add, hm1, one_smul]
  · rcases mul_eq_zero.mp hrest with h1 | h3
    · exfalso
      have ht1 : t = 1 := by linear_combination h1 - h2
      have e1 : t * t + -1 = (0 : K) := by linear_combination (t + 1) * ht1
      have e2 : -t = (1 : K) := by linear_combination -ht1 - h2
      have h3' : G ^ 3 = 1 := by rw [hp3, e1, e2, zero_smul, zero_add, one_smul]
      apply hsq1
      calc G ^ 2 = G ^ 2 * G ^ 3 := by rw [h3', mul_one]
        _ = G ^ 5 := (pow_add G 2 3).symm
        _ = 1 := hG5
    · exact h3

theorem gl2_trace_five {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (g s : Matrix.GeneralLinearGroup (Fin 2) K) (hg5 : g ^ 5 = 1) (hg1 : g ≠ 1)
    (hs : s * g * s⁻¹ = g⁻¹) :
    ∃ τ : K, τ ^ 2 + τ + 1 = 0 ∧
      (g : Matrix (Fin 2) (Fin 2) K) + ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = τ • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have h2 : (2 : K) = 0 := gl2t_two_eq_zero K hK
  have hmul : ∀ a b : Matrix.GeneralLinearGroup (Fin 2) K,
      ((a * b : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det
        = (a : Matrix (Fin 2) (Fin 2) K).det * (b : Matrix (Fin 2) (Fin 2) K).det := by
    intro a b
    rw [Units.val_mul, Matrix.det_mul]
  have e1 := hmul g g⁻¹
  rw [mul_inv_cancel, Units.val_one, Matrix.det_one] at e1
  have e2 := hmul s s⁻¹
  rw [mul_inv_cancel, Units.val_one, Matrix.det_one] at e2
  have e3 : ((s * g * s⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det
      = ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det := by
    rw [hs]
  rw [hmul, hmul] at e3
  have hdet : (g : Matrix (Fin 2) (Fin 2) K).det = 1 :=
    gl2t_scalar_det h2 _ _ _ _ e1 e2 e3
  have hCH : (g : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)
      = (g : Matrix (Fin 2) (Fin 2) K).trace • (g : Matrix (Fin 2) (Fin 2) K) - 1 := by
    have h := gl2t_cayley_hamilton (g : Matrix (Fin 2) (Fin 2) K)
    rw [hdet, one_smul] at h
    exact h
  have hG5 : (g : Matrix (Fin 2) (Fin 2) K) ^ 5 = 1 := by
    have h := congrArg Units.val hg5
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h
    exact h
  have hG1 : (g : Matrix (Fin 2) (Fin 2) K) ≠ 1 := fun h => hg1 (Units.ext h)
  have hquad := gl2t_trace_quad h2 (g : Matrix (Fin 2) (Fin 2) K)
    (g : Matrix (Fin 2) (Fin 2) K).trace (gl2t_pow_four K hK _) hCH hG5 hG1
  refine ⟨(g : Matrix (Fin 2) (Fin 2) K).trace, hquad, ?_⟩
  have hGH : (g : Matrix (Fin 2) (Fin 2) K)
      * ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : (g : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)
      * ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = ((g : Matrix (Fin 2) (Fin 2) K).trace • (g : Matrix (Fin 2) (Fin 2) K) - 1)
        * ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    rw [hCH]
  rw [mul_assoc, hGH, mul_one, sub_mul, smul_mul_assoc, hGH, one_mul] at h1
  exact eq_sub_iff_add_eq.mp h1

theorem scalar_contra {R D : Type*} [Ring R] [Field D] (d : D →+* R) (hd : Function.Injective d)
    (hchar : (2 : D) = 0) (ζ τ : D) (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) (hτ : τ ^ 2 + τ + 1 = 0)
    (u : Rˣ) (hu1 : (u : R) * d ζ * ((u⁻¹ : Rˣ) : R) = d ζ⁻¹)
    (hu2 : (u : R) * d τ * ((u⁻¹ : Rˣ) : R) = d τ) : False := by
  clear hchar
  have hinv : ζ⁻¹ = ζ ^ 2 := inv_eq_of_mul_eq_one_right (by linear_combination hζ3)
  have hζq : ζ ^ 2 + ζ + 1 = 0 := by
    have hf : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by linear_combination hζ3
    exact (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr hζ1)
  have hτc : τ = ζ ∨ τ = ζ ^ 2 := by
    have hf : (τ - ζ) * (τ - ζ ^ 2) = 0 := by linear_combination hτ - τ * hζq + hζ3
    rcases mul_eq_zero.mp hf with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  have hvu : ((u⁻¹ : Rˣ) : R) * (u : R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hmul : ∀ x y : R, (u : R) * (x * y) * ((u⁻¹ : Rˣ) : R)
      = ((u : R) * x * ((u⁻¹ : Rˣ) : R)) * ((u : R) * y * ((u⁻¹ : Rˣ) : R)) := by
    intro x y
    calc (u : R) * (x * y) * ((u⁻¹ : Rˣ) : R)
        = (u : R) * x * (((u⁻¹ : Rˣ) : R) * (u : R)) * y * ((u⁻¹ : Rˣ) : R) := by
          rw [hvu]; simp only [mul_one, mul_assoc]
      _ = ((u : R) * x * ((u⁻¹ : Rˣ) : R)) * ((u : R) * y * ((u⁻¹ : Rˣ) : R)) := by
          simp only [mul_assoc]
  have hF1 : (u : R) * d ζ * ((u⁻¹ : Rˣ) : R) = d (ζ ^ 2) := hu1.trans (congrArg d hinv)
  have hF2 : (u : R) * d (ζ ^ 2) * ((u⁻¹ : Rˣ) : R) = d ζ := by
    have e4 : ζ ^ 2 * ζ ^ 2 = ζ := by linear_combination ζ * hζ3
    calc (u : R) * d (ζ ^ 2) * ((u⁻¹ : Rˣ) : R)
        = (u : R) * (d ζ * d ζ) * ((u⁻¹ : Rˣ) : R) := by rw [map_pow, pow_two]
      _ = ((u : R) * d ζ * ((u⁻¹ : Rˣ) : R)) * ((u : R) * d ζ * ((u⁻¹ : Rˣ) : R)) := hmul _ _
      _ = d (ζ ^ 2) * d (ζ ^ 2) := by rw [hF1]
      _ = d (ζ ^ 2 * ζ ^ 2) := (map_mul d _ _).symm
      _ = d ζ := by rw [e4]
  have hκ : ζ ^ 2 = ζ := by
    rcases hτc with h | h
    · rw [h] at hu2
      exact (hd (hu2.symm.trans hF1)).symm
    · rw [h] at hu2
      exact hd (hu2.symm.trans hF2)
  have hz : ζ * (ζ - 1) = 0 := by linear_combination hκ
  rcases mul_eq_zero.mp hz with h0 | h1
  · rw [h0] at hζ3
    norm_num at hζ3
  · exact hζ1 (sub_eq_zero.mp h1)

end CFSG.Quasithin.H13.L828SixLem
