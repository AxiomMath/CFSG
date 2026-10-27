module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofOuter

public section

namespace CFSG.RankThree.PartTwo.Sec12.Hering129D4H

theorem sl2c2_two_eq_zero {k : Type} [Field k] [CharP k 2] : (2 : k) = 0 :=
  CharTwo.two_eq_zero

theorem sl2c2_fin_two_ext {R : Type*} {a b c d a' b' c' d' : R} (h1 : a = a')
    (h2 : b = b') (h3 : c = c') (h4 : d = d') :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) R) = !![a', b'; c', d'] := by
  subst h1 h2 h3 h4
  rfl

theorem sl2c2_fin_two_entries {R : Type*} {a b c d a' b' c' d' : R}
    (h : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) R) = !![a', b'; c', d']) :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' :=
  ⟨congrFun (congrFun h 0) 0, congrFun (congrFun h 0) 1, congrFun (congrFun h 1) 0,
    congrFun (congrFun h 1) 1⟩

theorem sl2c2_exists_sq_mul {k : Type} [Field k] [Finite k] [CharP k 2] {Δ : k}
    (hΔ : Δ ≠ 0) : ∃ s : k, s * s * Δ = 1 := by
  have hF : ringChar k = 2 := ringChar.eq k 2
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two hF Δ⁻¹
  exact ⟨s, by rw [← hs, inv_mul_cancel₀ hΔ]⟩

theorem sl2c2_conj_of_vec {k : Type} [Field k] [Finite k] [CharP k 2] {a b c e p q : k}
    (h2 : (2 : k) = 0) (hdet : a * e - b * c = 1) (htr : a + e + 1 = 0)
    (hΔ : c * p * p + (e - a) * p * q - b * q * q ≠ 0) :
    ∃ P : Matrix (Fin 2) (Fin 2) k, P.det = 1 ∧
      !![a, b; c, e] * P = P * !![0, 1; -1, -1] := by
  obtain ⟨s, hs⟩ := sl2c2_exists_sq_mul hΔ
  refine ⟨!![s * p, s * (a * p + b * q); s * q, s * (c * p + e * q)], ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hs
  · rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    apply sl2c2_fin_two_ext
    · linear_combination (s * (a * p + b * q)) * h2
    · linear_combination s * ((p * a + b * q) * htr - p * hdet - p * h2)
    · linear_combination (s * (c * p + e * q)) * h2
    · linear_combination s * ((p * c + q * e) * htr - q * hdet - q * h2)

theorem sl2c2_conj_matrix {k : Type} [Field k] [Finite k] [CharP k 2]
    {M : Matrix (Fin 2) (Fin 2) k} (hdet : M.det = 1) (hM3 : M ^ 3 = 1) (hM1 : M ≠ 1) :
    ∃ P : Matrix (Fin 2) (Fin 2) k, P.det = 1 ∧ M * P = P * !![0, 1; -1, -1] := by
  obtain ⟨a, b, c, e, rfl⟩ : ∃ a b c e : k, M = !![a, b; c, e] :=
    ⟨M 0 0, M 0 1, M 1 0, M 1 1, Matrix.eta_fin_two M⟩
  have h2 : (2 : k) = 0 := sl2c2_two_eq_zero
  rw [Matrix.det_fin_two_of] at hdet
  rw [pow_three', Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.one_fin_two] at hM3
  obtain ⟨E00, E01, E10, E11⟩ := sl2c2_fin_two_entries hM3
  have F1 : ((a + e) ^ 2 - 1) * a = (a + e) + 1 := by
    linear_combination E00 + (a + (a + e)) * hdet
  have F2 : ((a + e) ^ 2 - 1) * b = 0 := by
    linear_combination E01 + b * hdet
  have F3 : ((a + e) ^ 2 - 1) * c = 0 := by
    linear_combination E10 + c * hdet
  have F4 : ((a + e) ^ 2 - 1) * e = (a + e) + 1 := by
    linear_combination E11 + (e + (a + e)) * hdet
  have N : ¬ (b = 0 ∧ c = 0 ∧ a = e) := by
    rintro ⟨hb, hc, hae⟩
    apply hM1
    have haa : a * a = 1 := by
      rw [← hae, hb, hc] at hdet
      linear_combination hdet
    have ha : (a - 1) * (a - 1) = 0 := by
      linear_combination haa - (a - 1) * h2
    have ha' : a = 1 := sub_eq_zero.1 (mul_self_eq_zero.1 ha)
    rw [Matrix.one_fin_two]
    exact sl2c2_fin_two_ext ha' hb hc (hae.symm.trans ha')
  have G : (a + e) ^ 2 - 1 = 0 := by
    by_contra hD
    apply N
    have hb : b = 0 := (mul_eq_zero.1 F2).resolve_left hD
    have hc : c = 0 := (mul_eq_zero.1 F3).resolve_left hD
    exact ⟨hb, hc, mul_left_cancel₀ hD (F1.trans F4.symm)⟩
  have htr : a + e + 1 = 0 := by
    have hu : (a + e + 1) * (a + e + 1) = 0 := by
      linear_combination G + (a + e + 1) * h2
    exact mul_self_eq_zero.1 hu
  by_cases hc0 : c = 0
  · by_cases hb0 : b = 0
    · refine sl2c2_conj_of_vec (p := 1) (q := 1) h2 hdet htr ?_
      intro h
      apply N
      refine ⟨hb0, hc0, ?_⟩
      linear_combination -h + hc0 - hb0
    · refine sl2c2_conj_of_vec (p := 0) (q := 1) h2 hdet htr ?_
      intro h
      apply hb0
      linear_combination -h
  · refine sl2c2_conj_of_vec (p := 1) (q := 0) h2 hdet htr ?_
    intro h
    apply hc0
    linear_combination h

open CFSG.RankThree.PartTwo.Sec11.KS11Lie2Proof in
theorem sl2_exists_conj_sl2Three {k : Type} [Field k] [Finite k] [CharP k 2]
    {g : Matrix.SpecialLinearGroup (Fin 2) k} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) :
    ∃ x : Matrix.SpecialLinearGroup (Fin 2) k, x * g * x⁻¹ = sl2Three k := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) k).det = 1 := Matrix.SpecialLinearGroup.det_coe g
  have hM3 : (g : Matrix (Fin 2) (Fin 2) k) ^ 3 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hg3, Matrix.SpecialLinearGroup.coe_one]
  have hM1 : (g : Matrix (Fin 2) (Fin 2) k) ≠ 1 := fun h =>
    hg1 (Subtype.ext (h.trans Matrix.SpecialLinearGroup.coe_one.symm))
  obtain ⟨P, hPdet, hgP⟩ := sl2c2_conj_matrix hdet hM3 hM1
  obtain ⟨Q, hQP⟩ : ∃ Q : Matrix.SpecialLinearGroup (Fin 2) k,
      (Q : Matrix (Fin 2) (Fin 2) k) = P := ⟨⟨P, hPdet⟩, rfl⟩
  have hgQ : g * Q = Q * sl2Three k := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hQP]
    exact hgP
  refine ⟨Q⁻¹, ?_⟩
  rw [inv_inv, mul_assoc, hgQ, ← mul_assoc, inv_mul_cancel, one_mul]

end CFSG.RankThree.PartTwo.Sec12.Hering129D4H
