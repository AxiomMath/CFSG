module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Q8Sub

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Quasithin.A312U3

variable {F : Type*} [Field F]

theorem eq_neg_one_of_sq_eq_one (h2 : (2 : F) ≠ 0) {S : Matrix (Fin 2) (Fin 2) F}
    (hS : S * S = 1) (hdet : S.det = 1) (hne : S ≠ 1) : S = -1 := by
  have e00 := congrFun (congrFun hS 0) 0
  have e01 := congrFun (congrFun hS 0) 1
  have e10 := congrFun (congrFun hS 1) 0
  have e11 := congrFun (congrFun hS 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  rw [Matrix.det_fin_two] at hdet
  by_cases hsum : S 0 0 + S 1 1 = 0
  · exfalso
    have h11 : S 1 1 = -S 0 0 := by linear_combination hsum
    rw [h11] at hdet
    apply h2
    linear_combination -hdet - e00
  · have hq : S 0 1 = 0 := by
      have : S 0 1 * (S 0 0 + S 1 1) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right hsum
    have hr : S 1 0 = 0 := by
      have : S 1 0 * (S 0 0 + S 1 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right hsum
    rw [hq, hr] at hdet e00 e11
    have hpt : S 0 0 = S 1 1 := by
      have hp0 : S 0 0 ≠ 0 := fun h => by rw [h] at hdet; simp at hdet
      apply mul_left_cancel₀ hp0
      linear_combination e00 - hdet
    have hp1 : S 0 0 = 1 ∨ S 0 0 = -1 := by
      have : (S 0 0 - 1) * (S 0 0 + 1) = 0 := by linear_combination e00
      rcases mul_eq_zero.mp this with h | h
      · left; linear_combination h
      · right; linear_combination h
    rcases hp1 with h | h
    · exfalso
      apply hne
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hq, hr, h, ← hpt]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [hq, hr, h, ← hpt]

theorem quat_relations (h2 : (2 : F) ≠ 0) {c d : GL (Fin 2) F}
    (hc : (c : Matrix (Fin 2) (Fin 2) F).det = 1) (h : QuatPair c d) :
    (c : Matrix (Fin 2) (Fin 2) F) * c = -1 ∧ (d : Matrix (Fin 2) (Fin 2) F) * d = -1 ∧
      (d : Matrix (Fin 2) (Fin 2) F) * c = -((c : Matrix (Fin 2) (Fin 2) F) * d) := by
  obtain ⟨h4, hne, hd, hcd⟩ := h
  have hS : ((c : Matrix (Fin 2) (Fin 2) F) * c) * ((c : Matrix (Fin 2) (Fin 2) F) * c) = 1 := by
    have := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h4
    simpa [pow_succ, Units.val_mul, mul_assoc] using this
  have hdet : ((c : Matrix (Fin 2) (Fin 2) F) * c).det = 1 := by
    rw [Matrix.det_mul, hc, one_mul]
  have hneS : (c : Matrix (Fin 2) (Fin 2) F) * c ≠ 1 := fun h' => hne (Units.ext (by
    simpa [pow_two, Units.val_mul] using h'))
  have hc2 : (c : Matrix (Fin 2) (Fin 2) F) * c = -1 := eq_neg_one_of_sq_eq_one h2 hS hdet hneS
  have hd2 : (d : Matrix (Fin 2) (Fin 2) F) * d = -1 := by
    have := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hd
    simpa [pow_two, Units.val_mul, hc2] using this
  refine ⟨hc2, hd2, ?_⟩
  have hinv : ((c⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      -(c : Matrix (Fin 2) (Fin 2) F) := by
    have h1 : (c : Matrix (Fin 2) (Fin 2) F) * ((c⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        1 := by rw [← Units.val_mul, mul_inv_cancel]; rfl
    calc ((c⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        = ((c⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          ((c : Matrix (Fin 2) (Fin 2) F) * (-(c : Matrix (Fin 2) (Fin 2) F))) := by
          rw [mul_neg, hc2]; simp
      _ = -(c : Matrix (Fin 2) (Fin 2) F) := by
          rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel]; simp
  have hcd' : d * c = c⁻¹ * d := by
    rw [mul_inv_eq_iff_eq_mul] at hcd
    exact hcd
  have := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hcd'
  simp only [Units.val_mul, hinv] at this
  rw [this]
  simp

theorem trace_zero_of_anticomm (h2 : (2 : F) ≠ 0) {C D : Matrix (Fin 2) (Fin 2) F}
    (hC : C * C = -1) (hD : D * D = -1) (hDC : D * C = -(C * D)) : C 1 1 = -C 0 0 := by
  by_contra hne
  have hsum : C 0 0 + C 1 1 ≠ 0 := fun h => hne (by linear_combination h)
  have c00 := congrFun (congrFun hC 0) 0
  have c01 := congrFun (congrFun hC 0) 1
  have c10 := congrFun (congrFun hC 1) 0
  have c11 := congrFun (congrFun hC 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at c00 c01 c10 c11
  have hb : C 0 1 = 0 := by
    have : C 0 1 * (C 0 0 + C 1 1) = 0 := by linear_combination c01
    exact (mul_eq_zero.mp this).resolve_right hsum
  have he : C 1 0 = 0 := by
    have : C 1 0 * (C 0 0 + C 1 1) = 0 := by linear_combination c10
    exact (mul_eq_zero.mp this).resolve_right hsum
  have a0 : C 0 0 ≠ 0 := fun h => by
    rw [h, hb] at c00
    simp at c00
  have f0 : C 1 1 ≠ 0 := fun h => by
    rw [h, he] at c11
    simp at c11
  have d00 := congrFun (congrFun hDC 0) 0
  have d01 := congrFun (congrFun hDC 0) 1
  have d10 := congrFun (congrFun hDC 1) 0
  have d11 := congrFun (congrFun hDC 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, hb, he] at d00 d01 d10 d11
  have h00 : D 0 0 = 0 := by
    have : 2 * C 0 0 * D 0 0 = 0 := by linear_combination d00
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (mul_eq_zero.mp h) (by tauto)
    · exact h
  have h11 : D 1 1 = 0 := by
    have : 2 * C 1 1 * D 1 1 = 0 := by linear_combination d11
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (mul_eq_zero.mp h) (by tauto)
    · exact h
  have h01 : D 0 1 = 0 := by
    have : D 0 1 * (C 0 0 + C 1 1) = 0 := by linear_combination d01
    exact (mul_eq_zero.mp this).resolve_right hsum
  have h10 : D 1 0 = 0 := by
    have : D 1 0 * (C 0 0 + C 1 1) = 0 := by linear_combination d10
    exact (mul_eq_zero.mp this).resolve_right hsum
  have hDz : D = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
  rw [hDz] at hD
  have := congrFun (congrFun hD 0) 0
  simp at this

theorem scalar_of_commute_quat (h2 : (2 : F) ≠ 0) {C D A : Matrix (Fin 2) (Fin 2) F}
    (hC : C * C = -1) (hD : D * D = -1) (hDC : D * C = -(C * D))
    (hAC : A * C = C * A) (hAD : A * D = D * A) : ∃ x : F, A = Matrix.scalar (Fin 2) x := by
  have hCD : C * D = -(D * C) := by rw [hDC, neg_neg]
  have tC := trace_zero_of_anticomm h2 hC hD hDC
  have tD := trace_zero_of_anticomm h2 hD hC hCD
  obtain ⟨a, b, e, rfl⟩ : ∃ a b e : F, C = !![a, b; e, -a] :=
    ⟨C 0 0, C 0 1, C 1 0, by ext i j; fin_cases i <;> fin_cases j <;> simp [tC]⟩
  obtain ⟨a', b', e', rfl⟩ : ∃ a b e : F, D = !![a, b; e, -a] :=
    ⟨D 0 0, D 0 1, D 1 0, by ext i j; fin_cases i <;> fin_cases j <;> simp [tD]⟩
  obtain ⟨x, y, z, w, rfl⟩ : ∃ x y z w : F, A = !![x, y; z, w] :=
    ⟨A 0 0, A 0 1, A 1 0, A 1 1, Matrix.eta_fin_two A⟩
  have hR1 : a ^ 2 + b * e = -1 := by
    have := congrFun (congrFun hC 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this
  have hR2 : a' ^ 2 + b' * e' = -1 := by
    have := congrFun (congrFun hD 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this
  have hR3 : 2 * a * a' + b * e' + b' * e = 0 := by
    have := congrFun (congrFun hDC 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this
  have hC1 : y * e - b * z = 0 := by
    have := congrFun (congrFun hAC 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this
  have hC2 : b * (x - w) - 2 * a * y = 0 := by
    have := congrFun (congrFun hAC 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this
  have hC3 : e * (x - w) - 2 * a * z = 0 := by
    have := congrFun (congrFun hAC 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination -this
  have hD1 : y * e' - b' * z = 0 := by
    have := congrFun (congrFun hAD 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this
  have hD2 : b' * (x - w) - 2 * a' * y = 0 := by
    have := congrFun (congrFun hAD 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this
  have hD3 : e' * (x - w) - 2 * a' * z = 0 := by
    have := congrFun (congrFun hAD 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination -this
  set u := x - w with hu
  set L := u * a + 2 * y * e with hL
  set L' := u * a' + 2 * y * e' with hL'
  have K1 : L * a = -u := by linear_combination u * hR1 - e * hC2
  have K2 : L * b = -(2 * y) := by linear_combination a * hC2 + 2 * y * hR1
  have K3 : L * e = -(2 * z) := by linear_combination a * hC3 + 2 * z * hR1 + 2 * e * hC1
  have K1' : L' * a' = -u := by linear_combination u * hR2 - e' * hD2
  have K2' : L' * b' = -(2 * y) := by linear_combination a' * hD2 + 2 * y * hR2
  have K3' : L' * e' = -(2 * z) := by linear_combination a' * hD3 + 2 * z * hR2 + 2 * e' * hD1
  have hT : u ^ 2 + 4 * y * z = -L ^ 2 := by
    have : L ^ 2 * (a ^ 2 + b * e) = (L * a) ^ 2 + (L * b) * (L * e) := by ring
    rw [hR1, K1, K2, K3] at this
    linear_combination -this
  have hM : 2 * u ^ 2 + 8 * y * z = 0 := by
    have : L * L' * (2 * a * a' + b * e' + b' * e) =
        2 * (L * a) * (L' * a') + (L * b) * (L' * e') + (L' * b') * (L * e) := by ring
    rw [hR3, K1, K1', K2, K3', K2', K3] at this
    linear_combination -this
  have hL0 : L = 0 := by
    have : L ^ 2 = 0 := by
      have h2' : (2 : F) * (u ^ 2 + 4 * y * z) = 0 := by linear_combination hM
      have h3 : u ^ 2 + 4 * y * z = 0 := (mul_eq_zero.mp h2').resolve_left h2
      linear_combination hT - h3
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  have hu0 : u = 0 := by rw [hL0, zero_mul] at K1; linear_combination K1
  have hy0 : y = 0 := by
    rw [hL0, zero_mul] at K2
    have : 2 * y = 0 := by linear_combination K2
    exact (mul_eq_zero.mp this).resolve_left h2
  have hz0 : z = 0 := by
    rw [hL0, zero_mul] at K3
    have : 2 * z = 0 := by linear_combination K3
    exact (mul_eq_zero.mp this).resolve_left h2
  refine ⟨x, ?_⟩
  have hxw : w = x := by linear_combination -hu0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hy0, hz0, hxw]

end CFSG.Quasithin.E2P.Asc80
