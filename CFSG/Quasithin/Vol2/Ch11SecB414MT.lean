module

public import CFSG.Quasithin.Vol2.Ch11SecB414MS

public section

namespace CFSG.Quasithin.H13.Ch4.B414.M

open Matrix

variable {F : Type} [Field F]

abbrev blkC (C : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, 0, 0; 0, C 1 1, -C 1 0; 0, -C 0 1, C 0 0]

theorem isBlock_blkC (C : Matrix (Fin 2) (Fin 2) F) : IsBlock (blkC C) := ⟨rfl, rfl, rfl, rfl⟩

theorem det_blkC (C : Matrix (Fin 2) (Fin 2) F) : (blkC C).det = C.det := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp
  ring

theorem rhoA_blkC (C : Matrix (Fin 2) (Fin 2) F) : rhoA (blkC C) = C := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [rhoA, adjugate_fin_three]

abbrev e12 (F : Type) [Field F] : Matrix (Fin 3) (Fin 3) F := !![0, 0, 0; 0, 0, 1; 0, 0, 0]

abbrev aU (F : Type) [Field F] : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, 1, 1; 0, 0, 1]

abbrev aW (l m : F) : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, 0, m; 0, l, 0]

abbrev aV (l : F) : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, 1, 0; 0, l, 1]

variable [CharP F 2]

theorem cnj_aU_sub {M : Matrix (Fin 3) (Fin 3) F} (hM : IsBlock M) :
    cnj (aU F) M - M = M 2 1 • hatI F + (M 2 2 + M 1 1 + M 2 1) • e12 F := by
  obtain ⟨h01, h02, h10, h20⟩ := hM
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp only [cnj, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
      Fin.sum_univ_three]
    simp [adjugate_fin_three, h01, h02, h10, h20]
    try first
      | linear_combination (-M 2 1) * h2
      | linear_combination (-M 2 1 - M 1 1) * h2

theorem cnj_sum {l m x y : F} (hlm : l * m = 1) :
    (x • hatI F + y • e12 F) + cnj (aW l m) (x • hatI F + y • e12 F) +
      cnj (aV l) (x • hatI F + y • e12 F) = (x + l * y) • hatI F := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp only [cnj, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_three]
    simp [adjugate_fin_three]
    try first
      | linear_combination (-(y * l)) * h2 - x * hlm
      | linear_combination (-(l ^ 2 * y)) * h2
      | linear_combination -x * hlm
      | linear_combination y * h2

omit [CharP F 2] in
theorem isBlock_aU : IsBlock (aU F) := ⟨rfl, rfl, rfl, rfl⟩

omit [CharP F 2] in
theorem isBlock_aW (l m : F) : IsBlock (aW l m) := ⟨rfl, rfl, rfl, rfl⟩

omit [CharP F 2] in
theorem isBlock_aV (l : F) : IsBlock (aV l) := ⟨rfl, rfl, rfl, rfl⟩

omit [CharP F 2] in
theorem det_aU : (aU F).det = 1 := by
  rw [Matrix.det_fin_three]
  simp

theorem det_aW {l m : F} (hlm : l * m = 1) : (aW l m).det = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [Matrix.det_fin_three]
  simp
  linear_combination -hlm - h2

omit [CharP F 2] in
theorem det_aV (l : F) : (aV l).det = 1 := by
  rw [Matrix.det_fin_three]
  simp

omit [CharP F 2] in
theorem cnj_aV_21 {M : Matrix (Fin 3) (Fin 3) F} (hM : IsBlock M) (h12 : M 1 2 = 0)
    (h21 : M 2 1 = 0) : cnj (aV 1) M 2 1 = M 1 1 - M 2 2 := by
  obtain ⟨h01, h02, h10, h20⟩ := hM
  simp only [cnj, Matrix.mul_apply, Fin.sum_univ_three]
  simp [adjugate_fin_three, h01, h02, h10, h20, h12, h21]
  ring

theorem cnj_aW_21 {M : Matrix (Fin 3) (Fin 3) F} (hM : IsBlock M) :
    cnj (aW 1 1) M 2 1 = M 1 2 := by
  obtain ⟨h01, h02, h10, h20⟩ := hM
  simp only [cnj, Matrix.mul_apply, Fin.sum_univ_three]
  simp [adjugate_fin_three, h01, h02, h10, h20]
  linear_combination (-M 1 2) * (CharTwo.two_eq_zero : (2 : F) = 0)

theorem exists_hatI {ν : F} (hν0 : ν ≠ 0) (hν1 : ν ≠ 1) (S : AddSubgroup (Matrix (Fin 3) (Fin 3) F))
    (hS : ∀ M ∈ S, IsBlock M ∧ M.trace = 0)
    (hcnj : ∀ A : Matrix (Fin 3) (Fin 3) F, IsBlock A → A.det = 1 → ∀ M ∈ S, cnj A M ∈ S)
    {M : Matrix (Fin 3) (Fin 3) F} (hM : M ∈ S) (hM0 : M ≠ 0) :
    ∃ x : F, x ≠ 0 ∧ x • hatI F ∈ S := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have step : ∀ M ∈ S, M 2 1 ≠ 0 → ∃ x : F, x ≠ 0 ∧ x • hatI F ∈ S := by
    intro M hM hz
    have hD : cnj (aU F) M - M ∈ S := S.sub_mem (hcnj _ isBlock_aU det_aU M hM) hM
    rw [cnj_aU_sub (hS M hM).1] at hD
    have key : ∀ l : F, l ≠ 0 → (M 2 1 + l * (M 2 2 + M 1 1 + M 2 1)) • hatI F ∈ S := by
      intro l hl
      have hlm : l * l⁻¹ = 1 := mul_inv_cancel₀ hl
      rw [← cnj_sum hlm]
      exact S.add_mem (S.add_mem hD (hcnj _ (isBlock_aW _ _) (det_aW hlm) _ hD))
        (hcnj _ (isBlock_aV _) (det_aV _) _ hD)
    by_cases h1 : M 2 1 + 1 * (M 2 2 + M 1 1 + M 2 1) = 0
    · refine ⟨_, fun h => hz ?_, key ν hν0⟩
      have : (1 - ν) * M 2 1 = 0 := by linear_combination h - ν * h1
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (Ne.symm hν1))
    · exact ⟨_, h1, key 1 one_ne_zero⟩
  obtain ⟨h01, h02, h10, h20⟩ := (hS M hM).1
  have htr := (hS M hM).2
  rw [Matrix.trace_fin_three] at htr
  by_cases hz : M 2 1 = 0
  · by_cases hy : M 1 2 = 0
    · by_cases hxw : M 1 1 = M 2 2
      · have h00 : M 0 0 = 0 := by linear_combination htr - hxw - (M 2 2) * h2
        refine ⟨M 1 1, fun h0 => hM0 ?_, ?_⟩
        · have h22 : M 2 2 = 0 := by rw [← hxw]; exact h0
          ext i j
          fin_cases i <;> fin_cases j <;> simp [h00, h01, h02, h10, h20, hy, hz, h0, h22]
        · convert hM using 1
          ext i j
          fin_cases i <;> fin_cases j <;> simp [h00, h01, h02, h10, h20, hy, hz, hxw]
      · refine step _ (hcnj _ (isBlock_aV 1) (det_aV 1) M hM) ?_
        rw [cnj_aV_21 (hS M hM).1 hy hz]
        exact sub_ne_zero.mpr hxw
    · refine step _ (hcnj _ (isBlock_aW 1 1) (det_aW (one_mul 1)) M hM) ?_
      rw [cnj_aW_21 (hS M hM).1]
      exact hy
  · exact step M hM hz

omit [CharP F 2] in
theorem cnj_hatI {A : Matrix (Fin 3) (Fin 3) F} (hA : IsBlock A) (hdet : A.det = 1) :
    cnj A (hatI F) = hatI F := by
  obtain ⟨h01, h02, h10, h20⟩ := hA
  have hd := hdet
  rw [det_of_par h10 h20] at hd
  ext i j
  simp only [cnj, Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp [adjugate_fin_three, h01, h02, h10, h20] <;>
    first | ring1 | linear_combination -hd | linear_combination hd

end CFSG.Quasithin.H13.Ch4.B414.M
