module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof

open Matrix Polynomial

theorem fin_two_eq_of {α : Type*} {a b c d a' b' c' d' : α} (h₁ : a = a') (h₂ : b = b')
    (h₃ : c = c') (h₄ : d = d') : !![a, b; c, d] = !![a', b'; c', d'] := by
  rw [h₁, h₂, h₃, h₄]

variable {F : Type*} [Field F]

theorem exists_entries (B : SpecialLinearGroup (Fin 2) F) :
    ∃ a b c d : F, (B : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] ∧ a * d - b * c = 1 := by
  refine ⟨(B : Matrix (Fin 2) (Fin 2) F) 0 0, (B : Matrix (Fin 2) (Fin 2) F) 0 1,
    (B : Matrix (Fin 2) (Fin 2) F) 1 0, (B : Matrix (Fin 2) (Fin 2) F) 1 1, eta_fin_two _, ?_⟩
  have h := B.2
  rwa [det_fin_two] at h

theorem trace_eq_neg_one_of_pow_three {a b c d : F} (hdet : a * d - b * c = 1)
    (h3 : !![a, b; c, d] * !![a, b; c, d] * !![a, b; c, d] = 1)
    (h1 : !![a, b; c, d] ≠ (1 : Matrix (Fin 2) (Fin 2) F)) : a + d = -1 := by
  rw [mul_fin_two, mul_fin_two, one_fin_two] at h3
  have e00 := congrFun (congrFun h3 0) 0
  have e01 := congrFun (congrFun h3 0) 1
  have e10 := congrFun (congrFun h3 1) 0
  have e11 := congrFun (congrFun h3 1) 1
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one] at e00 e01 e10 e11
  by_cases ht : (a + d) ^ 2 = 1
  · linear_combination (-1 : F) * e00 + a * ht - (2 * a + d) * hdet
  · exfalso
    have ht' : (a + d) ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr ht
    have hb : b = 0 := by
      have : b * ((a + d) ^ 2 - 1) = 0 := by linear_combination e01 + b * hdet
      exact (mul_eq_zero.mp this).resolve_right ht'
    have hc : c = 0 := by
      have : c * ((a + d) ^ 2 - 1) = 0 := by linear_combination e10 + c * hdet
      exact (mul_eq_zero.mp this).resolve_right ht'
    subst hb hc
    have ha3 : a ^ 3 = 1 := by linear_combination e00
    have had : a * d = 1 := by linear_combination hdet
    have hd : d = a ^ 2 := by linear_combination a ^ 2 * had - d * ha3
    have ha : a = 1 := by
      by_contra ha1
      have hq : a ^ 2 + a + 1 = 0 := by
        have : (a - 1) * (a ^ 2 + a + 1) = 0 := by linear_combination ha3
        exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ha1)
      apply ht
      rw [hd]
      linear_combination (a + 2) * ha3 + hq
    apply h1
    rw [one_fin_two]
    exact fin_two_eq_of ha rfl rfl (by rw [hd, ha]; ring)

theorem exists_frame_of_trace {a b c d : F} (h3 : (3 : F) ≠ 0) (hdet : a * d - b * c = 1)
    (htr : a + d = -1) :
    ∃ P : Matrix (Fin 2) (Fin 2) F, P.det ≠ 0 ∧
      !![a, b; c, d] * P = P * !![0, -1; 1, -1] := by
  by_cases hb : b = 0
  · by_cases hc : c = 0
    · refine ⟨!![1, a; 1, d], ?_, ?_⟩
      · rw [det_fin_two_of]
        intro h
        apply h3
        have had : a - d = 0 := by linear_combination -h
        linear_combination (-4 : F) * hdet + (a + d - 1) * htr - (a - d) * had - 4 * c * hb
      · rw [mul_fin_two, mul_fin_two]
        refine fin_two_eq_of ?_ ?_ ?_ ?_
        · rw [hb]; ring
        · linear_combination a * htr - hdet + (d - c) * hb
        · rw [hc]; ring
        · linear_combination d * htr - hdet + (a - b) * hc
    · refine ⟨!![1, a; 0, c], ?_, ?_⟩
      · rw [det_fin_two_of]
        simpa using hc
      · rw [mul_fin_two, mul_fin_two]
        refine fin_two_eq_of (by ring) ?_ (by ring) ?_
        · linear_combination a * htr - hdet
        · linear_combination c * htr
  · refine ⟨!![0, b; 1, d], ?_, ?_⟩
    · rw [det_fin_two_of]
      simpa using hb
    · rw [mul_fin_two, mul_fin_two]
      refine fin_two_eq_of (by ring) ?_ (by ring) ?_
      · linear_combination b * htr
      · linear_combination d * htr - hdet

theorem exists_normForm_eq [Finite F] (h3 : (3 : F) ≠ 0) (u : F) :
    ∃ x y : F, x ^ 2 - x * y + y ^ 2 = u := by
  classical
  have : Fintype F := Fintype.ofFinite F
  by_cases h2 : ringChar F = 2
  · obtain ⟨x, hx⟩ := FiniteField.isSquare_of_char_two h2 u
    exact ⟨x, 0, by rw [hx]; ring⟩
  · have h2' : (2 : F) ≠ 0 := Ring.two_ne_zero h2
    have hf : degree (X ^ 2 : F[X]) = 2 := by rw [degree_X_pow]; norm_num
    have hg : degree (C 3 * X ^ 2 - C (4 * u) : F[X]) = 2 := by
      rw [degree_sub_C (by rw [degree_C_mul_X_pow 2 h3]; norm_num), degree_C_mul_X_pow 2 h3]
      norm_num
    obtain ⟨a, b, hab⟩ :=
      FiniteField.exists_root_sum_quadratic hf hg (FiniteField.odd_card_of_char_ne_two h2)
    simp only [eval_pow, eval_X, eval_sub, eval_mul, eval_C] at hab
    obtain ⟨h, hh⟩ : ∃ h : F, 2 * h = 1 := ⟨2⁻¹, mul_inv_cancel₀ h2'⟩
    refine ⟨(a + b) * h, b, ?_⟩
    linear_combination h ^ 2 * hab + (h * a * b - b ^ 2 * (h + 1) + u * (2 * h + 1)) * hh

theorem det_smul_one_add_smul {a b c d : F} (hdet : a * d - b * c = 1) (htr : a + d = -1)
    (x y : F) :
    (x • (1 : Matrix (Fin 2) (Fin 2) F) + y • !![a, b; c, d]).det = x ^ 2 - x * y + y ^ 2 := by
  rw [det_fin_two]
  simp
  linear_combination y ^ 2 * hdet + x * y * htr

theorem exists_conj_of_pow_three [Finite F] (h3 : (3 : F) ≠ 0)
    {B B' : SpecialLinearGroup (Fin 2) F} (hB : B ^ 3 = 1) (hB1 : B ≠ 1) (hB' : B' ^ 3 = 1)
    (hB'1 : B' ≠ 1) : ∃ A : SpecialLinearGroup (Fin 2) F, A * B * A⁻¹ = B' := by
  have hM : ∀ X : SpecialLinearGroup (Fin 2) F, X ^ 3 = 1 → X ≠ 1 →
      ∃ a b c d : F, (X : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] ∧ a * d - b * c = 1 ∧
        a + d = -1 := by
    intro X hX hX1
    obtain ⟨a, b, c, d, hX', hdet⟩ := exists_entries X
    refine ⟨a, b, c, d, hX', hdet, trace_eq_neg_one_of_pow_three hdet ?_ ?_⟩
    · have h := congrArg (fun Y : SpecialLinearGroup (Fin 2) F => (Y : Matrix (Fin 2) (Fin 2) F)) hX
      simp only [SpecialLinearGroup.coe_pow, SpecialLinearGroup.coe_one] at h
      rw [← hX', ← h, pow_succ, pow_two]
    · intro h
      apply hX1
      ext i j
      rw [hX', h, SpecialLinearGroup.coe_one]
  obtain ⟨a, b, c, d, hBM, hdet, htr⟩ := hM B hB hB1
  obtain ⟨a', b', c', d', hBM', hdet', htr'⟩ := hM B' hB' hB'1
  obtain ⟨P, hP, hBP⟩ := exists_frame_of_trace h3 hdet htr
  obtain ⟨P', hP', hBP'⟩ := exists_frame_of_trace h3 hdet' htr'
  set M : Matrix (Fin 2) (Fin 2) F := ↑B with hMdef
  set M' : Matrix (Fin 2) (Fin 2) F := ↑B' with hM'def
  rw [← hBM] at hBP
  rw [← hBM'] at hBP'
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  set A₀ := P' * P⁻¹ with hA₀
  have hA₀B : A₀ * M = M' * A₀ := by
    have hPinv : P⁻¹ * M = !![0, -1; 1, -1] * P⁻¹ := by
      calc P⁻¹ * M = P⁻¹ * M * (P * P⁻¹) := by rw [mul_nonsing_inv P hPu, Matrix.mul_one]
        _ = P⁻¹ * (M * P) * P⁻¹ := by simp only [Matrix.mul_assoc]
        _ = P⁻¹ * (P * !![0, -1; 1, -1]) * P⁻¹ := by rw [hBP]
        _ = !![0, -1; 1, -1] * P⁻¹ := by
            rw [← Matrix.mul_assoc, nonsing_inv_mul P hPu, Matrix.one_mul]
    rw [hA₀, Matrix.mul_assoc, hPinv, ← Matrix.mul_assoc, ← hBP', Matrix.mul_assoc]
  have hdet₀ : A₀.det ≠ 0 := by
    rw [hA₀, det_mul, det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero hP' (inv_ne_zero hP)
  obtain ⟨x, y, hxy⟩ := exists_normForm_eq h3 (A₀.det)⁻¹
  set A₁ := A₀ * (x • (1 : Matrix (Fin 2) (Fin 2) F) + y • M) with hA₁
  have hA₁det : A₁.det = 1 := by
    rw [hA₁, det_mul, hBM, det_smul_one_add_smul hdet htr, hxy, mul_inv_cancel₀ hdet₀]
  have hA₁B : A₁ * M = M' * A₁ := by
    have hc : (x • (1 : Matrix (Fin 2) (Fin 2) F) + y • M) * M =
        M * (x • (1 : Matrix (Fin 2) (Fin 2) F) + y • M) := by
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    rw [hA₁, Matrix.mul_assoc, hc, ← Matrix.mul_assoc, hA₀B, Matrix.mul_assoc]
  let A : SpecialLinearGroup (Fin 2) F := ⟨A₁, hA₁det⟩
  refine ⟨A, ?_⟩
  have hAB : A * B = B' * A := Subtype.ext hA₁B
  rw [hAB, mul_inv_cancel_right]

end CFSG.RankThree.PartTwo.Sec11.Item1118Res3Proof
