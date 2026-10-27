module

public import CFSG.LieType.Universal.Spin.Chevalley.Basic

public section

namespace CFSG.Quasithin.Vol2.Ch11.O10

open Matrix CFSG.LieType.Universal.Spin

variable {F : Type*} [Field F]

theorem two_eq_zero_of_charP [CharP F 2] : (2 : F) = 0 := by
  exact_mod_cast CharP.cast_eq_zero F 2

theorem upperSL2_mul_self [CharP F 2] (a : F) : upperSL2 a * upperSL2 a = 1 := by
  rw [← upperSL2_add, show a + a = 0 by linear_combination a * two_eq_zero_of_charP (F := F),
    upperSL2_zero]

theorem upperSL2_inv [CharP F 2] (a : F) : (upperSL2 a)⁻¹ = upperSL2 a :=
  inv_eq_of_mul_eq_one_right (upperSL2_mul_self a)

theorem lowerSL2_mul_self [CharP F 2] (a : F) : lowerSL2 a * lowerSL2 a = 1 := by
  rw [← lowerSL2_add, show a + a = 0 by linear_combination a * two_eq_zero_of_charP (F := F),
    lowerSL2_zero]

theorem upperSL2_commute (a b : F) : upperSL2 a * upperSL2 b = upperSL2 b * upperSL2 a := by
  rw [← upperSL2_add, ← upperSL2_add, add_comm]

theorem weyl_conj_upper [CharP F 2] (c : F) :
    (upperSL2 1 * lowerSL2 1 * upperSL2 1) * upperSL2 c *
      (upperSL2 1 * lowerSL2 1 * upperSL2 (1 : F)) = lowerSL2 c := by
  have h2 := two_eq_zero_of_charP (F := F)
  apply Subtype.ext
  simp
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · linear_combination (3 + c) * h2
  · linear_combination (6 + 2 * c) * h2
  · linear_combination 2 * h2
  · linear_combination (3 + c) * h2

theorem lower_upper_cube [CharP F 2] :
    (lowerSL2 (1 : F) * upperSL2 1) * (lowerSL2 1 * upperSL2 1) * (lowerSL2 1 * upperSL2 1) =
      1 := by
  have h2 := two_eq_zero_of_charP (F := F)
  apply Subtype.ext
  simp [Matrix.one_fin_two]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · linear_combination 2 * h2
  · linear_combination 4 * h2
  · linear_combination 4 * h2
  · linear_combination 6 * h2

theorem mul_entry (M N : SpecialLinearGroup (Fin 2) F) (i j : Fin 2) :
    (↑(M * N) : Matrix (Fin 2) (Fin 2) F) i j = M i 0 * N 0 j + M i 1 * N 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem upper_entry (M : SpecialLinearGroup (Fin 2) F) (i : Fin 2) :
    (↑(M * upperSL2 (1 : F)) : Matrix (Fin 2) (Fin 2) F) i 0 = M i 0 ∧
      (↑(M * upperSL2 (1 : F)) : Matrix (Fin 2) (Fin 2) F) i 1 = M i 0 + M i 1 := by
  rw [mul_entry, mul_entry]
  simp

theorem entry_eq_of_sq [CharP F 2] (M : SpecialLinearGroup (Fin 2) F) (hM2 : M * M = 1) :
    M 1 1 = M 0 0 := by
  have h2 := two_eq_zero_of_charP (F := F)
  have e : ∀ i j, (↑(M * M) : Matrix (Fin 2) (Fin 2) F) i j =
      (↑(1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j := fun i j => by
    rw [hM2]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  rw [mul_entry] at e00 e01 e10 e11
  simp at e00 e01 e10 e11
  by_contra hne
  have hs : M 0 0 + M 1 1 ≠ 0 := fun h => hne (by linear_combination h - M 0 0 * h2)
  have hb : M 0 1 = 0 := by
    have : M 0 1 * (M 0 0 + M 1 1) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right hs
  have hc : M 1 0 = 0 := by
    have : M 1 0 * (M 0 0 + M 1 1) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right hs
  rw [hb, zero_mul, add_zero] at e00
  rw [hb, mul_zero, zero_add] at e11
  have ha : (M 0 0 + 1) ^ 2 = 0 := by linear_combination e00 + (M 0 0 + 1) * h2
  have hd : (M 1 1 + 1) ^ 2 = 0 := by linear_combination e11 + (M 1 1 + 1) * h2
  apply hs
  linear_combination (pow_eq_zero_iff (n := 2) (by norm_num)).mp ha +
    (pow_eq_zero_iff (n := 2) (by norm_num)).mp hd - h2

theorem eq_conj_lower [CharP F 2] (M : SpecialLinearGroup (Fin 2) F) (hM2 : M * M = 1)
    (hM3 : (M * upperSL2 1) * (M * upperSL2 1) * (M * upperSL2 1) = 1) (hMu : M ≠ upperSL2 1) :
    M = upperSL2 (M 0 0 + 1) * lowerSL2 1 * (upperSL2 (M 0 0 + 1))⁻¹ := by
  have h2 := two_eq_zero_of_charP (F := F)
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by rw [← det_fin_two]; exact M.2
  have had := entry_eq_of_sq M hM2
  have e00 : (↑(M * M) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by rw [hM2]; simp
  rw [mul_entry] at e00
  obtain ⟨N, hN⟩ : ∃ N, N = M * upperSL2 1 := ⟨_, rfl⟩
  rw [← hN] at hM3
  have n00 : (N : Matrix (Fin 2) (Fin 2) F) 0 0 = M 0 0 := by rw [hN]; exact (upper_entry M 0).1
  have n01 : (N : Matrix (Fin 2) (Fin 2) F) 0 1 = M 0 0 + M 0 1 := by
    rw [hN]; exact (upper_entry M 0).2
  have n10 : (N : Matrix (Fin 2) (Fin 2) F) 1 0 = M 1 0 := by rw [hN]; exact (upper_entry M 1).1
  have n11 : (N : Matrix (Fin 2) (Fin 2) F) 1 1 = M 1 0 + M 1 1 := by
    rw [hN]; exact (upper_entry M 1).2
  have hNN : ∀ i j, (↑(N * N) : Matrix (Fin 2) (Fin 2) F) i j =
      M 1 0 * N i j + (↑(1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j := by
    intro i j
    rw [mul_entry]
    fin_cases i <;> fin_cases j <;> simp [n00, n01, n10, n11, had]
    · linear_combination e00
    · linear_combination (M 0 0 * (M 0 0 + M 0 1)) * h2
    · linear_combination (M 0 0 * M 1 0) * h2
    · linear_combination e00 + (M 1 0 * M 0 0) * h2
  have hN3 : ∀ i j, (↑(N * N * N) : Matrix (Fin 2) (Fin 2) F) i j =
      (M 1 0 * M 1 0 + 1) * N i j +
        M 1 0 * (↑(1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j := by
    intro i j
    have h := hNN i j
    rw [mul_entry] at h
    rw [mul_entry, hNN, hNN]
    fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> linear_combination (M 1 0) * h
  have f00 := hN3 0 0
  have f01 := hN3 0 1
  have f10 := hN3 1 0
  rw [hM3] at f00 f01 f10
  simp [n00, n01, n10] at f00 f01 f10
  have hc1 : M 1 0 = 1 := by
    by_contra hne
    have hc0 : M 1 0 = 0 := by
      rcases f10 with h | h
      · have hsq : (M 1 0 + 1) ^ 2 = 0 := by linear_combination h + M 1 0 * h2
        have h1 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp hsq
        exact absurd (by linear_combination h1 - h2 : M 1 0 = 1) hne
      · exact h
    rw [hc0] at f00 f01
    simp at f00 f01
    have hb : M 0 1 = 1 := by linear_combination f01 + f00 - (1 : F) * h2
    apply hMu
    apply Subtype.ext
    rw [Matrix.eta_fin_two (M : Matrix (Fin 2) (Fin 2) F)]
    simp [had, hc0, hb, ← f00]
  rw [upperSL2_inv]
  apply Subtype.ext
  rw [Matrix.eta_fin_two (M : Matrix (Fin 2) (Fin 2) F)]
  rw [had, hc1] at hdet
  simp [had, hc1]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · linear_combination -h2
  · linear_combination -hdet - (2 * M 0 0 + 2) * h2
  · linear_combination -h2

theorem exists_conj_of_fix_upper [CharP F 2] (α : MulAut (SpecialLinearGroup (Fin 2) F))
    (hα : ∀ c : F, α (upperSL2 c) = upperSL2 c) :
    ∃ s : F, ∀ M, α M = upperSL2 s * M * (upperSL2 s)⁻¹ := by
  set M := α (lowerSL2 1) with hMdef
  have hM2 : M * M = 1 := by rw [hMdef, ← map_mul, lowerSL2_mul_self, map_one]
  have hM3 : (M * upperSL2 1) * (M * upperSL2 1) * (M * upperSL2 1) = 1 := by
    rw [hMdef, ← hα 1, ← map_mul, ← map_mul, ← map_mul, lower_upper_cube, map_one]
  have hMu : M ≠ upperSL2 1 := by
    intro h
    have h1 : α (lowerSL2 1) = α (upperSL2 1) := by rw [← hMdef, h, hα]
    have h3 := congrArg (fun N : SpecialLinearGroup (Fin 2) F => N 1 0) (α.injective h1)
    simp at h3
  set s := M 0 0 + 1 with hs
  have hMs : M = upperSL2 s * lowerSL2 1 * upperSL2 s := by
    rw [eq_conj_lower M hM2 hM3 hMu, upperSL2_inv]
  refine ⟨s, fun N => ?_⟩
  have hw : α (upperSL2 1 * lowerSL2 1 * upperSL2 1) =
      upperSL2 s * (upperSL2 1 * lowerSL2 1 * upperSL2 1) * upperSL2 s := by
    rw [map_mul, map_mul, hα, ← hMdef, hMs]
    have hc := upperSL2_commute (1 : F) s
    calc upperSL2 1 * (upperSL2 s * lowerSL2 1 * upperSL2 s) * upperSL2 1
        = (upperSL2 1 * upperSL2 s) * lowerSL2 1 * (upperSL2 s * upperSL2 1) := by group
      _ = (upperSL2 s * upperSL2 1) * lowerSL2 1 * (upperSL2 1 * upperSL2 s) := by
          rw [hc, upperSL2_commute s 1]
      _ = _ := by group
  have hv : ∀ c, α (lowerSL2 c) = upperSL2 s * lowerSL2 c * (upperSL2 s)⁻¹ := by
    intro c
    rw [← weyl_conj_upper c, map_mul, map_mul, hα, hw, upperSL2_inv]
    have hc := upperSL2_commute s c
    calc upperSL2 s * (upperSL2 1 * lowerSL2 1 * upperSL2 1) * upperSL2 s * upperSL2 c *
          (upperSL2 s * (upperSL2 1 * lowerSL2 1 * upperSL2 1) * upperSL2 s)
        = upperSL2 s * (upperSL2 1 * lowerSL2 1 * upperSL2 1) * (upperSL2 s * upperSL2 c *
          upperSL2 s) * (upperSL2 1 * lowerSL2 1 * upperSL2 1) * upperSL2 s := by group
      _ = upperSL2 s * ((upperSL2 1 * lowerSL2 1 * upperSL2 1) * upperSL2 c *
          (upperSL2 1 * lowerSL2 1 * upperSL2 1)) * upperSL2 s := by
          rw [hc, mul_assoc (upperSL2 c), upperSL2_mul_self, mul_one]
          group
  have hu : ∀ c, α (upperSL2 c) = upperSL2 s * upperSL2 c * (upperSL2 s)⁻¹ := fun c => by
    rw [hα, upperSL2_commute s c, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨a, b, c, d, rfl⟩ := exists_eq_lowerSL2_mul_upperSL2_mul_lowerSL2_mul_upperSL2 N
  rw [map_mul, map_mul, map_mul, hv, hv, hu, hu]
  group

end CFSG.Quasithin.Vol2.Ch11.O10
