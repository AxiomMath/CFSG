module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.PartOne.Q1327F

open Matrix Polynomial

variable {K : Type} [Field K]

theorem adjugate_fin_two_eq (A : Matrix (Fin 2) (Fin 2) K) :
    adjugate A = (A 0 0 + A 1 1) • (1 : Matrix (Fin 2) (Fin 2) K) - A := by
  rw [adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.sub_apply]

theorem exists_matrix_conj_aux [Finite K] (h2 : (2 : K) ≠ 0) (a b c d : K)
    (hdet : a * d - b * c = 1)
    (ht : (a + d) ^ 2 ≠ 4) :
    ∃ W : Matrix (Fin 2) (Fin 2) K, W.det = 1 ∧
      W * !![a, b; c, d] = !![d, -b; -c, a] * W := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨x, y, u, hE1, hdj⟩ :
      ∃ x y u : K, (a - d) * x + c * y + b * u = 0 ∧ -x ^ 2 - y * u ≠ 0 := by
    by_cases hc0 : c = 0
    · by_cases hb0 : b = 0
      · exact ⟨0, 1, 1, by simp [hc0, hb0], by simp⟩
      · exact ⟨b, 0, -(a - d), by ring, by simp [hb0]⟩
    · exact ⟨c, -(a - d), 0, by ring, by simp [hc0]⟩
  have hd₀ne : 4 - (a + d) ^ 2 ≠ 0 := sub_ne_zero.2 (Ne.symm ht)
  have hcard : Fintype.card K % 2 = 1 := by
    have hrc : ringChar K ≠ 2 := fun hr => h2 ((ringChar.spec K 2).2 (by rw [hr]))
    exact FiniteField.odd_card_of_char_ne_two hrc
  obtain ⟨a', b', hab⟩ := FiniteField.exists_root_sum_quadratic (R := K)
    (f := X ^ 2 - C (-x ^ 2 - y * u)⁻¹) (g := C (4 - (a + d) ^ 2) * X ^ 2)
    (degree_X_pow_sub_C (by norm_num) _) (degree_C_mul_X_pow 2 hd₀ne) hcard
  simp only [eval_sub, eval_pow, eval_X, eval_C, eval_mul] at hab
  have hdetM : (!![a' + b' * (a - d), 2 * b' * b; 2 * b' * c, a' - b' * (a - d)] :
      Matrix (Fin 2) (Fin 2) K).det = (-x ^ 2 - y * u)⁻¹ := by
    rw [Matrix.det_fin_two_of]
    linear_combination hab + 4 * b' ^ 2 * hdet
  have hdetj : (!![x, y; u, -x] : Matrix (Fin 2) (Fin 2) K).det = -x ^ 2 - y * u := by
    rw [Matrix.det_fin_two_of]
    ring
  refine ⟨!![a' + b' * (a - d), 2 * b' * b; 2 * b' * c, a' - b' * (a - d)] * !![x, y; u, -x], ?_,
    ?_⟩
  · rw [Matrix.det_mul, hdetM, hdetj]
    exact inv_mul_cancel₀ hdj
  · have hjA : (!![x, y; u, -x] : Matrix (Fin 2) (Fin 2) K) * !![a, b; c, d] =
        !![d, -b; -c, a] * !![x, y; u, -x] := by
      ext i k
      fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | ring1 | linear_combination hE1
    have hMA : (!![a' + b' * (a - d), 2 * b' * b; 2 * b' * c, a' - b' * (a - d)] :
        Matrix (Fin 2) (Fin 2) K) =
        (a' - b' * (a + d)) • (1 : Matrix (Fin 2) (Fin 2) K) + (2 * b') • !![a, b; c, d] := by
      ext i k
      fin_cases i <;> fin_cases k <;> simp <;> ring
    have hadj : (!![d, -b; -c, a] : Matrix (Fin 2) (Fin 2) K) =
        (a + d) • (1 : Matrix (Fin 2) (Fin 2) K) - !![a, b; c, d] := by
      ext i k
      fin_cases i <;> fin_cases k <;> simp
    set A : Matrix (Fin 2) (Fin 2) K := !![a, b; c, d] with hA
    set M : Matrix (Fin 2) (Fin 2) K :=
      !![a' + b' * (a - d), 2 * b' * b; 2 * b' * c, a' - b' * (a - d)] with hM
    have hcomm : Commute M A := by
      rw [hMA]
      exact ((Commute.one_left A).smul_left _).add_left ((Commute.refl A).smul_left _)
    have hcomm' : Commute M (!![d, -b; -c, a] : Matrix (Fin 2) (Fin 2) K) := by
      rw [hadj]
      exact ((Commute.one_right M).smul_right _).sub_right hcomm
    calc M * !![x, y; u, -x] * A = M * (!![x, y; u, -x] * A) := mul_assoc _ _ _
      _ = M * (!![d, -b; -c, a] * !![x, y; u, -x]) := by rw [hjA]
      _ = (M * !![d, -b; -c, a]) * !![x, y; u, -x] := (mul_assoc _ _ _).symm
      _ = (!![d, -b; -c, a] * M) * !![x, y; u, -x] := by rw [hcomm'.eq]
      _ = !![d, -b; -c, a] * (M * !![x, y; u, -x]) := mul_assoc _ _ _

theorem exists_inv_conj_sl2_odd [Finite K] (h2 : (2 : K) ≠ 0) (z : SpecialLinearGroup (Fin 2) K)
    (ht : ((z : Matrix (Fin 2) (Fin 2) K) 0 0 + (z : Matrix (Fin 2) (Fin 2) K) 1 1) ^ 2 ≠ 4) :
    ∃ w : SpecialLinearGroup (Fin 2) K, w * z * w⁻¹ = z⁻¹ := by
  have hdet : (z : Matrix (Fin 2) (Fin 2) K) 0 0 * (z : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (z : Matrix (Fin 2) (Fin 2) K) 0 1 * (z : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
    have := z.2
    rw [Matrix.det_fin_two] at this
    exact this
  obtain ⟨W, hWdet, hW⟩ := exists_matrix_conj_aux h2 _ _ _ _ hdet ht
  have hAeq : (z : Matrix (Fin 2) (Fin 2) K) = !![(z : Matrix (Fin 2) (Fin 2) K) 0 0,
      (z : Matrix (Fin 2) (Fin 2) K) 0 1; (z : Matrix (Fin 2) (Fin 2) K) 1 0,
      (z : Matrix (Fin 2) (Fin 2) K) 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  obtain ⟨W', hW'⟩ : ∃ W' : SpecialLinearGroup (Fin 2) K, (W' : Matrix (Fin 2) (Fin 2) K) = W :=
    ⟨⟨W, hWdet⟩, rfl⟩
  refine ⟨W', ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two, hW']
  rw [hAeq] at *
  simpa using hW

end CFSG.RankThree.PartOne.Q1327F
