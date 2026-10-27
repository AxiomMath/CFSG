module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentData

public section

namespace CFSG.OddTranspositions.PartThree.Wong

private theorem sl5_ext_iff {x y : SL5} :
    x = y ↔ (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0 = y 0 0 ∧
      (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 1 = y 0 1 ∧
      (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0 = y 1 0 ∧
      (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 1 = y 1 1 := by
  rw [Matrix.SpecialLinearGroup.ext_iff]
  simp [Fin.forall_fin_two, and_assoc]

private theorem sl5_det (x : SL5) :
    (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0 * (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 1 -
      (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 1 * (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0 =
        1 := by
  have := x.2
  rwa [Matrix.det_fin_two] at this

private theorem exists_sl5 (p q r s : ZMod 5) (h : p * s - q * r = 1) :
    ∃ g : SL5, (g : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0 = p ∧
      (g : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 1 = q ∧
      (g : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0 = r ∧
      (g : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 1 = s :=
  ⟨⟨!![p, q; r, s], by rwa [Matrix.det_fin_two_of]⟩, rfl, rfl, rfl, rfl⟩

private theorem hM_val : (hM : Matrix (Fin 2) (Fin 2) (ZMod 5)) = !![2, 0; 0, 3] := rfl

private theorem cM_val : (cM : Matrix (Fin 2) (Fin 2) (ZMod 5)) = !![0, -1; 1, 0] := rfl

set_option synthInstance.maxSize 1000 in
private theorem trace_zero_aux (a b c d : ZMod 5) (h1 : a * a + b * c = -1)
    (h2 : a * b + b * d = 0) (h3 : c * a + d * c = 0) (h4 : c * b + d * d = -1)
    (hdet : a * d - b * c = 1) : d = -a := by
  revert a b c d
  decide

set_option synthInstance.maxSize 1000 in
private theorem eigen_aux (a b c : ZMod 5) (h : a * a + b * c = -1) :
    ∃ p q r s : ZMod 5, p * s - q * r = 1 ∧ p * a + q * c = 2 * p ∧ p * b + -(q * a) = 2 * q ∧
      r * a + s * c = 3 * r ∧ r * b + -(s * a) = 3 * s := by
  by_cases ha : a = 3
  · refine ⟨c, -1, 1, b, ?_⟩
    subst ha
    revert b c
    decide
  · refine ⟨(a - 3) * (a + 2) ^ 3, b * (a + 2) ^ 3, c, -a - 2, ?_⟩
    revert a b c
    decide

theorem hM_sq : hM ^ 2 = -1 := by decide

theorem cM_sq : cM ^ 2 = -1 := by decide

theorem hM_mul_cM_sq : (hM * cM) ^ 2 = -1 := by decide

theorem cM_inv_mul_hM_mul_cM : cM⁻¹ * hM * cM = hM⁻¹ := by decide

theorem neg_hM : -hM = hM⁻¹ := by decide

theorem commute_hM_iff (x : SL5) : Commute x hM ↔ x = 1 ∨ x = -1 ∨ x = hM ∨ x = -hM := by
  rw [commute_iff_eq]
  simp only [sl5_ext_iff, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  simp [hM_val]
  have hd := sl5_det x
  generalize (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0 = a at *
  generalize (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 1 = b at *
  generalize (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0 = c at *
  generalize (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 1 = d at *
  revert a b c d
  set_option synthInstance.maxSize 1000 in
  decide +revert

theorem conj_hM_eq_inv_iff (x : SL5) :
    x * hM * x⁻¹ = hM⁻¹ ↔ x = cM ∨ x = -cM ∨ x = hM * cM ∨ x = -(hM * cM) := by
  rw [mul_inv_eq_iff_eq_mul, ← neg_hM]
  simp only [sl5_ext_iff, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.neg_apply, Matrix.mul_apply, Fin.sum_univ_two]
  simp [hM_val, cM_val]
  have hd := sl5_det x
  generalize (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0 = a at *
  generalize (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 1 = b at *
  generalize (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 0 = c at *
  generalize (x : Matrix (Fin 2) (Fin 2) (ZMod 5)) 1 1 = d at *
  revert a b c d
  set_option synthInstance.maxSize 1000 in
  decide +revert

theorem exists_conj_hM_of_sq_eq_neg_one {x : SL5} (hx : x ^ 2 = -1) :
    ∃ g : SL5, g * x * g⁻¹ = hM := by
  suffices H : ∃ g : SL5, g * x = hM * g by
    obtain ⟨g, hg⟩ := H
    exact ⟨g, by rw [hg, mul_assoc, mul_inv_cancel, mul_one]⟩
  have hdet := sl5_det x
  rw [pow_two, sl5_ext_iff] at hx
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply] at hx
  simp at hx
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have hd := trace_zero_aux _ _ _ _ h1 h2 h3 h4 hdet
  obtain ⟨p, q, r, s, hps, e1, e2, e3, e4⟩ := eigen_aux _ _ _ h1
  obtain ⟨g, g00, g01, g10, g11⟩ := exists_sl5 p q r s hps
  refine ⟨g, ?_⟩
  rw [sl5_ext_iff]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, g00, g01, g10,
    g11]
  simp [hM_val, hd]
  exact ⟨e1, e2, e3, e4⟩

end CFSG.OddTranspositions.PartThree.Wong
