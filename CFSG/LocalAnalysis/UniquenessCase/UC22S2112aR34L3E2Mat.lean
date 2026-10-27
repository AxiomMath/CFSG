module

public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryNorm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix

private theorem uc22s2112r34_block_zero {K : Type} [Field K] {g : Matrix (Fin 3) (Fin 3) K}
    {A : Matrix (Fin 2) (Fin 2) K} (hA1 : (A - 1).det ≠ 0)
    (hgA : g * !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1] =
      !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1] * g) :
    g 0 2 = 0 ∧ g 1 2 = 0 ∧ g 2 0 = 0 ∧ g 2 1 = 0 := by
  have hdet : (A - 1).det = (A 0 0 - 1) * (A 1 1 - 1) - A 0 1 * A 1 0 := by
    rw [Matrix.det_fin_two]
    simp
  have hA1' : (A 0 0 - 1) * (A 1 1 - 1) - A 0 1 * A 1 0 ≠ 0 := by rwa [← hdet]
  have e02 := congrFun (congrFun hgA 0) 2
  have e12 := congrFun (congrFun hgA 1) 2
  have e20 := congrFun (congrFun hgA 2) 0
  have e21 := congrFun (congrFun hgA 2) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at e02 e12 e20 e21
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : g 0 2 * ((A 0 0 - 1) * (A 1 1 - 1) - A 0 1 * A 1 0) = 0 := by
      linear_combination (1 - A 1 1) * e02 + A 0 1 * e12
    exact (mul_eq_zero.mp h).resolve_right hA1'
  · have h : g 1 2 * ((A 0 0 - 1) * (A 1 1 - 1) - A 0 1 * A 1 0) = 0 := by
      linear_combination (1 - A 0 0) * e12 + A 1 0 * e02
    exact (mul_eq_zero.mp h).resolve_right hA1'
  · have h : g 2 0 * ((A 0 0 - 1) * (A 1 1 - 1) - A 0 1 * A 1 0) = 0 := by
      linear_combination (A 1 1 - 1) * e20 - A 1 0 * e21
    exact (mul_eq_zero.mp h).resolve_right hA1'
  · have h : g 2 1 * ((A 0 0 - 1) * (A 1 1 - 1) - A 0 1 * A 1 0) = 0 := by
      linear_combination (A 0 0 - 1) * e21 - A 0 1 * e20
    exact (mul_eq_zero.mp h).resolve_right hA1'

private theorem uc22s2112r34_cube_data {K : Type} [Field K] {g : Matrix (Fin 3) (Fin 3) K}
    {c : K} (h02 : g 0 2 = 0) (h12 : g 1 2 = 0) (h20 : g 2 0 = 0) (h21 : g 2 1 = 0)
    (hg3 : g ^ 3 = Matrix.scalar (Fin 3) c) :
    g = !![g 0 0, g 0 1, 0; g 1 0, g 1 1, 0; 0, 0, g 2 2] ∧ g 2 2 ^ 3 = c ∧
      (!![g 0 0, g 0 1; g 1 0, g 1 1] : Matrix (Fin 2) (Fin 2) K) ^ 3 = c • 1 := by
  have hg_eq : g = !![g 0 0, g 0 1, 0; g 1 0, g 1 1, 0; 0, 0, g 2 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h02, h12, h20, h21]
  have e00 : g 0 0 ^ 3 + 2 * g 0 0 * g 0 1 * g 1 0 + g 0 1 * g 1 0 * g 1 1 = c := by
    have h := congrFun (congrFun hg3 0) 0
    rw [hg_eq] at h
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply] at h
    linear_combination h
  have e01 : g 0 0 ^ 2 * g 0 1 + g 0 1 ^ 2 * g 1 0 + g 0 0 * g 0 1 * g 1 1 +
      g 0 1 * g 1 1 ^ 2 = 0 := by
    have h := congrFun (congrFun hg3 0) 1
    rw [hg_eq] at h
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply] at h
    linear_combination h
  have e10 : g 1 0 * g 0 0 ^ 2 + g 1 1 * g 1 0 * g 0 0 + g 1 0 ^ 2 * g 0 1 +
      g 1 1 ^ 2 * g 1 0 = 0 := by
    have h := congrFun (congrFun hg3 1) 0
    rw [hg_eq] at h
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply] at h
    linear_combination h
  have e11 : g 1 0 * g 0 0 * g 0 1 + 2 * (g 0 1 * g 1 0 * g 1 1) + g 1 1 ^ 3 = c := by
    have h := congrFun (congrFun hg3 1) 1
    rw [hg_eq] at h
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply] at h
    linear_combination h
  refine ⟨hg_eq, ?_, ?_⟩
  · have h := congrFun (congrFun hg3 2) 2
    rw [hg_eq] at h
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply] at h
    linear_combination h
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination e00
    · linear_combination e01
    · linear_combination e10
    · linear_combination e11

private theorem uc22s2112r34_smul_cube {K : Type} [Field K] {M : Matrix (Fin 2) (Fin 2) K}
    {α c : K} (hα : α ≠ 0) (hα3 : α ^ 3 = c) (hM3 : M ^ 3 = c • 1) :
    (α⁻¹ • M) ^ 3 = 1 := by
  rw [smul_pow, hM3, smul_smul, ← hα3,
    show (α⁻¹) ^ 3 * α ^ 3 = 1 by rw [← mul_pow, inv_mul_cancel₀ hα, one_pow], one_smul]

private theorem uc22s2112r34_det_conj {K : Type} [Field K] (u w : Fin 2 → K) (t : K) :
    (!![u 0, 0, t * w 0; u 1, 0, t * w 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K).det =
      t * (u 1 * w 0 - u 0 * w 1) := by
  rw [Matrix.det_fin_three]
  simp
  ring

private theorem uc22s2112r34_conj_diag {K : Type} [Field K] {B : Matrix (Fin 2) (Fin 2) K}
    {d α t : K} {u w : Fin 2 → K} (hu : B *ᵥ u = u) (hw : B *ᵥ w = d • w) :
    (!![α * B 0 0, α * B 0 1, 0; α * B 1 0, α * B 1 1, 0; 0, 0, α] : Matrix (Fin 3) (Fin 3) K) *
        !![u 0, 0, t * w 0; u 1, 0, t * w 1; 0, 1, 0] =
      !![u 0, 0, t * w 0; u 1, 0, t * w 1; 0, 1, 0] * Matrix.diagonal ![α, α, α * d] := by
  have hu0 := congrFun hu 0
  have hu1 := congrFun hu 1
  have hw0 := congrFun hw 0
  have hw1 := congrFun hw 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    at hu0 hu1 hw0 hw1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply] <;>
    first
      | linear_combination α * hu0
      | linear_combination α * hu1
      | linear_combination (α * t) * hw0
      | linear_combination (α * t) * hw1

private theorem uc22s2112r34_two_cases {K : Type} [Field K] {B : Matrix (Fin 2) (Fin 2) K}
    (hB : B ^ 3 = 1) :
    (∃ μ : K, B = μ • 1) ∨ B.det = 1 ∨
      (B.det ≠ 1 ∧ ∃ u w : Fin 2 → K, u ≠ 0 ∧ w ≠ 0 ∧ B *ᵥ u = u ∧ B *ᵥ w = B.det • w ∧
        u 0 * w 1 - u 1 * w 0 ≠ 0) := by
  set t : K := B 0 0 + B 1 1 with ht
  set d : K := B 0 0 * B 1 1 - B 0 1 * B 1 0 with hd
  have hBdet : B.det = d := by
    rw [Matrix.det_fin_two, hd]
  have hCH : B * B = t • B - d • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ht, hd] <;> ring
  have hcube : B ^ 3 = (t ^ 2 - d) • B - (t * d) • 1 := by
    have h3 : B ^ 3 = (B * B) * B := by rw [pow_succ, pow_two]
    rw [h3, hCH]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ht, hd] <;> ring
  have hrel : (t ^ 2 - d) • B = (1 + t * d) • 1 := by
    have h := hB
    rw [hcube] at h
    have h2 : (t ^ 2 - d) • B = 1 + (t * d) • 1 := by
      rw [← sub_eq_iff_eq_add]
      exact h
    calc (t ^ 2 - d) • B = 1 + (t * d) • 1 := h2
      _ = (1 + t * d) • 1 := by rw [add_smul, one_smul]
  by_cases hcase : t ^ 2 - d = 0
  · have hd_eq : d = t ^ 2 := by linear_combination -hcase
    have h1td : 1 + t * d = 0 := by
      have h := congrFun (congrFun hrel 0) 0
      rw [hcase, zero_smul] at h
      simpa using h.symm
    have ht3 : t ^ 3 = -1 := by
      have h : t * d = t ^ 3 := by rw [hd_eq]; ring
      rw [h] at h1td
      linear_combination h1td
    by_cases hd1 : d = 1
    · exact Or.inr (Or.inl (by rw [hBdet, hd1]))
    · refine Or.inr (Or.inr ⟨by rw [hBdet]; exact hd1, ?_⟩)
      have ht2 : t ^ 2 - t + 1 = 0 := by
        have hfac : (t + 1) * (t ^ 2 - t + 1) = 0 := by linear_combination ht3
        rcases mul_eq_zero.mp hfac with h | h
        · exfalso
          apply hd1
          have ht1 : t = -1 := by linear_combination h
          rw [hd_eq, ht1]
          ring
        · exact h
      have hd1' : (B - 1).det = 0 := by
        have he : (B - 1).det = d - t + 1 := by
          rw [Matrix.det_fin_two]
          simp [hd, ht]
          ring
        rw [he, hd_eq, ht2]
      have hdd : (B - d • 1).det = 0 := by
        have he : (B - d • 1).det = d * (d - t + 1) := by
          rw [Matrix.det_fin_two]
          simp [hd, ht]
          ring
        rw [he, hd_eq, ht2]
        ring
      obtain ⟨u, hu0, hueq⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd1'
      obtain ⟨w, hw0, hweq⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdd
      have hu : B *ᵥ u = u := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hueq
        exact hueq
      have hw : B *ᵥ w = d • w := by
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hweq
        exact hweq
      have hind : u 0 * w 1 - u 1 * w 0 ≠ 0 := by
        intro hcon
        obtain ⟨lam, hl0, hl1⟩ : ∃ lam : K, w 0 = lam * u 0 ∧ w 1 = lam * u 1 := by
          by_cases hu0' : u 0 = 0
          · have hu1 : u 1 ≠ 0 := by
              intro h1
              apply hu0
              funext i
              fin_cases i <;> simp [hu0', h1]
            refine ⟨w 1 / u 1, ?_, ?_⟩
            · have h : u 1 * w 0 = 0 := by linear_combination -hcon + w 1 * hu0'
              have hw00 : w 0 = 0 := (mul_eq_zero.mp h).resolve_left hu1
              rw [hw00, hu0', mul_zero]
            · field_simp
          · refine ⟨w 0 / u 0, ?_, ?_⟩
            · field_simp
            · have h : u 0 * w 1 = u 1 * w 0 := by linear_combination hcon
              field_simp
              linear_combination h
        have hl : w = lam • u := by
          funext i
          fin_cases i <;> simp [hl0, hl1, Pi.smul_apply, smul_eq_mul]
        have hw1 : B *ᵥ w = w := by
          rw [hl, Matrix.mulVec_smul, hu]
        have h2 : w = d • w := hw1.symm.trans hw
        have h3 : (d - 1) • w = 0 := by rw [sub_smul, one_smul, ← h2, sub_self]
        have hwz : w = 0 := (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hd1)
        exact hw0 hwz
      have hneed : B.det ≠ 1 := by rw [hBdet]; exact hd1
      have hw' : B *ᵥ w = B.det • w := by rw [hBdet]; exact hw
      have hmain : ∃ u w : Fin 2 → K, u ≠ 0 ∧ w ≠ 0 ∧ B *ᵥ u = u ∧
          B *ᵥ w = B.det • w ∧ u 0 * w 1 - u 1 * w 0 ≠ 0 :=
        ⟨u, w, hu0, hw0, hu, hw', hind⟩
      exact hmain
  · refine Or.inl ⟨(1 + t * d) / (t ^ 2 - d), ?_⟩
    have h1 : (t ^ 2 - d)⁻¹ • ((t ^ 2 - d) • B) = (t ^ 2 - d)⁻¹ • ((1 + t * d) • 1) := by
      rw [hrel]
    rw [smul_smul, inv_mul_cancel₀ hcase, one_smul, smul_smul] at h1
    rw [h1, div_eq_inv_mul]

private theorem uc22s2112r34_solve {K : Type} [Field K] {X Y a0 a1 b0 b1 : K}
    (h1 : X * a0 + Y * a1 = 0) (h2 : X * b0 + Y * b1 = 0) (hdet : a0 * b1 - a1 * b0 ≠ 0) :
    X = 0 ∧ Y = 0 := by
  have hX : X * (a0 * b1 - a1 * b0) = 0 := by linear_combination b1 * h1 - a1 * h2
  have hY : Y * (a0 * b1 - a1 * b0) = 0 := by linear_combination -b0 * h1 + a0 * h2
  exact ⟨(mul_eq_zero.mp hX).resolve_right hdet, (mul_eq_zero.mp hY).resolve_right hdet⟩

private theorem uc22s2112r34_inner_pres {p f : ℕ} {K : Type} [Field K]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K)
    {B : Matrix (Fin 2) (Fin 2) K} (hB : (B.map h.bar)ᵀ * B = 1) (x y : Fin 2 → K) :
    h.bar ((B *ᵥ x) 0) * (B *ᵥ y) 0 + h.bar ((B *ᵥ x) 1) * (B *ᵥ y) 1 =
      h.bar (x 0) * y 0 + h.bar (x 1) * y 1 := by
  have h00 := congrFun (congrFun hB 0) 0
  have h01 := congrFun (congrFun hB 0) 1
  have h10 := congrFun (congrFun hB 1) 0
  have h11 := congrFun (congrFun hB 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
    Matrix.map_apply] at h00 h01 h10 h11
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  linear_combination (h.bar (x 0) * y 0) * h00 + (h.bar (x 0) * y 1) * h01 +
    (h.bar (x 1) * y 0) * h10 + (h.bar (x 1) * y 1) * h11

private theorem uc22s2112r34_unitary_smul_inv {p f : ℕ} {K : Type} [Field K]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K)
    {M : Matrix (Fin 2) (Fin 2) K} {α : K} (hα : h.bar α * α = 1)
    (hM : (M.map h.bar)ᵀ * M = 1) :
    ((α⁻¹ • M).map h.bar)ᵀ * (α⁻¹ • M) = 1 := by
  have hb : h.bar α⁻¹ * α⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, hα, inv_one]
  have hmap : (α⁻¹ • M).map h.bar = h.bar α⁻¹ • M.map h.bar := by
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hmap, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hM]
  rw [smul_smul, hb, one_smul]

private theorem uc22s2112r34_block_unitary {p f : ℕ} {K : Type} [Field K]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K)
    {g : Matrix (Fin 3) (Fin 3) K}
    (h02 : g 0 2 = 0) (h12 : g 1 2 = 0) (h20 : g 2 0 = 0) (h21 : g 2 1 = 0)
    (hgu : (g.map h.bar)ᵀ * g = 1) :
    ((!![g 0 0, g 0 1; g 1 0, g 1 1] : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ *
        !![g 0 0, g 0 1; g 1 0, g 1 1] = 1 ∧ h.bar (g 2 2) * g 2 2 = 1 := by
  have e00 : h.bar (g 0 0) * g 0 0 + h.bar (g 1 0) * g 1 0 = 1 := by
    have h1 := congrFun (congrFun hgu 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.map_apply,
      h20] at h1
    exact h1
  have e01 : h.bar (g 0 0) * g 0 1 + h.bar (g 1 0) * g 1 1 = 0 := by
    have h1 := congrFun (congrFun hgu 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.map_apply,
      h20, h21] at h1
    exact h1
  have e10 : h.bar (g 0 1) * g 0 0 + h.bar (g 1 1) * g 1 0 = 0 := by
    have h1 := congrFun (congrFun hgu 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.map_apply,
      h20, h21] at h1
    exact h1
  have e11 : h.bar (g 0 1) * g 0 1 + h.bar (g 1 1) * g 1 1 = 1 := by
    have h1 := congrFun (congrFun hgu 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.map_apply,
      h21] at h1
    exact h1
  have e22 : h.bar (g 2 2) * g 2 2 = 1 := by
    have h1 := congrFun (congrFun hgu 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.map_apply,
      h02, h12] at h1
    exact h1
  refine ⟨?_, e22⟩
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.one_apply] using e00
  · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.one_apply] using e01
  · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.one_apply] using e10
  · simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.one_apply] using e11


theorem uc22s2112r34_det_sub_one_ne_zero {K : Type} [Field K] {A : Matrix (Fin 2) (Fin 2) K}
    (hA : A.det = 1) {r : ℕ} (hrK : (r : K) ≠ 0) (hAr : A ^ r = 1) (hA1 : A ≠ 1) :
    (A - 1).det ≠ 0 := by
  intro hdet
  have h00 : (A - 1) 0 0 = A 0 0 - 1 := by simp
  have h01 : (A - 1) 0 1 = A 0 1 := by simp
  have h10 : (A - 1) 1 0 = A 1 0 := by simp
  have h11 : (A - 1) 1 1 = A 1 1 - 1 := by simp
  have hh : (A 0 0 - 1) * (A 1 1 - 1) - A 0 1 * A 1 0 = 0 := by
    have h := hdet
    rw [Matrix.det_fin_two, h00, h01, h10, h11] at h
    exact h
  have hA' : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact hA
  have htrace : A 0 0 + A 1 1 = 2 := by
    linear_combination -hh + hA'
  set N : Matrix (Fin 2) (Fin 2) K := A - 1 with hN
  have hN2 : N * N = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hN, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply] <;>
      first
        | linear_combination (A 0 0 - 1) * htrace - hh
        | linear_combination A 0 1 * htrace
        | linear_combination A 1 0 * htrace
        | linear_combination (A 1 1 - 1) * htrace - hh
  have hA_eq : A = 1 + N := by
    rw [hN]
    abel
  have hpow : ∀ k : ℕ, A ^ k = 1 + (k : K) • N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, hA_eq]
      have hmul : (1 + (k : K) • N) * (1 + N) = 1 + ((k : K) + 1) • N := by
        have h1 : (1 + (k : K) • N) * (1 + N) = 1 + N + (k : K) • N := by
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
            Matrix.smul_mul, hN2, smul_zero, add_zero]
          abel
        rw [h1]
        conv_rhs => rw [add_smul (k : K) 1 N, one_smul]
        abel
      rw [hmul, Nat.cast_add, Nat.cast_one]
  have hAr' : 1 + (r : K) • N = 1 := by
    rw [← hpow r]
    exact hAr
  have hN0 : N = 0 := by
    refine (smul_eq_zero.mp ?_).resolve_left hrK
    have h4 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M - 1) hAr'
    simpa [add_sub_cancel_left] using h4
  have hAone : A = 1 := by
    rw [hN] at hN0
    exact sub_eq_zero.mp hN0
  exact hA1 hAone

theorem uc22s2112r34_cube_or_conj_diag {K : Type} [Field K] {g : Matrix (Fin 3) (Fin 3) K}
    (hg : g.det ≠ 0) {c : K} (hg3 : g ^ 3 = Matrix.scalar (Fin 3) c)
    {A : Matrix (Fin 2) (Fin 2) K} (hA1 : (A - 1).det ≠ 0)
    (hgA : g * !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1] =
      !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1] * g) :
    (∃ b : K, g.det = b ^ 3) ∨
      ∃ (P : Matrix (Fin 3) (Fin 3) K) (μ ν : K), P.det = 1 ∧
        g * P = P * Matrix.diagonal ![μ, μ, ν] := by
  obtain ⟨h02, h12, h20, h21⟩ := uc22s2112r34_block_zero hA1 hgA
  obtain ⟨hg_eq, hα3', hM3⟩ := uc22s2112r34_cube_data h02 h12 h20 h21 hg3
  set α : K := g 2 2 with hαdef
  have hα3 : α ^ 3 = c := by rw [hαdef]; exact hα3'
  have hdetg : g.det = α * (g 0 0 * g 1 1 - g 0 1 * g 1 0) := by
    rw [hg_eq, Matrix.det_fin_three]
    simp
    ring
  have hα : α ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdetg
    exact hg hdetg
  set B : Matrix (Fin 2) (Fin 2) K := α⁻¹ • !![g 0 0, g 0 1; g 1 0, g 1 1] with hBdef
  have hB00 : B 0 0 = α⁻¹ * g 0 0 := by simp [hBdef]
  have hB01 : B 0 1 = α⁻¹ * g 0 1 := by simp [hBdef]
  have hB10 : B 1 0 = α⁻¹ * g 1 0 := by simp [hBdef]
  have hB11 : B 1 1 = α⁻¹ * g 1 1 := by simp [hBdef]
  have hBdet : B.det * α ^ 2 = g 0 0 * g 1 1 - g 0 1 * g 1 0 := by
    rw [Matrix.det_fin_two, hB00, hB01, hB10, hB11]
    field_simp
  have hgα : g = !![α * B 0 0, α * B 0 1, 0; α * B 1 0, α * B 1 1, 0; 0, 0, α] := by
    rw [hg_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hB00, hB01, hB10, hB11, mul_inv_cancel_left₀ hα]
  have hB3 : B ^ 3 = 1 := uc22s2112r34_smul_cube hα hα3 hM3
  rcases uc22s2112r34_two_cases hB3 with ⟨μ', hμ'⟩ | hdet1 | ⟨hd1, u, w, hu, hw, hBu, hBw, hind⟩
  · refine Or.inr ⟨1, α * μ', α, by simp, ?_⟩
    rw [Matrix.mul_one, Matrix.one_mul, hgα]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hμ', Matrix.smul_apply]
  · refine Or.inl ⟨α, ?_⟩
    rw [hdetg, ← hBdet, hdet1]
    ring
  · set t : K := -(u 0 * w 1 - u 1 * w 0)⁻¹ with ht
    set P : Matrix (Fin 3) (Fin 3) K :=
      !![u 0, 0, t * w 0; u 1, 0, t * w 1; 0, 1, 0] with hP
    have hPdet : P.det = 1 := by
      rw [hP, uc22s2112r34_det_conj u w t, ht]
      field_simp
      ring
    have hconj : g * P = P * Matrix.diagonal ![α, α, α * B.det] := by
      rw [hgα, hP]
      exact uc22s2112r34_conj_diag hBu hBw
    exact Or.inr ⟨P, α, α * B.det, hPdet, hconj⟩

theorem uc22s2112r34_cube_or_conj_diag_unitary {p f : ℕ} {K : Type} [Field K]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K)
    {g : Matrix (Fin 3) (Fin 3) K} (hgu : (g.map h.bar)ᵀ * g = 1)
    {c : K} (hg3 : g ^ 3 = Matrix.scalar (Fin 3) c)
    {A : Matrix (Fin 2) (Fin 2) K} (hA1 : (A - 1).det ≠ 0)
    (hgA : g * !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1] =
      !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1] * g) :
    (∃ b : K, g.det = b ^ 3) ∨
      ∃ (P : Matrix (Fin 3) (Fin 3) K) (μ ν : K), P.det = 1 ∧ (P.map h.bar)ᵀ * P = 1 ∧
        g * P = P * Matrix.diagonal ![μ, μ, ν] := by
  have hgdet : g.det ≠ 0 := by
    have hone : ((g.map h.bar)ᵀ).det * g.det = 1 := by
      rw [← Matrix.det_mul, hgu, Matrix.det_one]
    intro h0
    rw [h0, mul_zero] at hone
    exact zero_ne_one hone
  obtain ⟨h02, h12, h20, h21⟩ := uc22s2112r34_block_zero hA1 hgA
  obtain ⟨hg_eq, hα3', hM3⟩ := uc22s2112r34_cube_data h02 h12 h20 h21 hg3
  obtain ⟨hMbar, hbarα⟩ := uc22s2112r34_block_unitary h h02 h12 h20 h21 hgu
  set α : K := g 2 2 with hαdef
  have hbarα' : h.bar α * α = 1 := by rw [hαdef]; exact hbarα
  have hα3 : α ^ 3 = c := by rw [hαdef]; exact hα3'
  have hα : α ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hbarα'
    exact zero_ne_one hbarα'
  have hdetg : g.det = α * (g 0 0 * g 1 1 - g 0 1 * g 1 0) := by
    rw [hg_eq, Matrix.det_fin_three]
    simp
    ring
  set B : Matrix (Fin 2) (Fin 2) K := α⁻¹ • !![g 0 0, g 0 1; g 1 0, g 1 1] with hBdef
  have hB00 : B 0 0 = α⁻¹ * g 0 0 := by simp [hBdef]
  have hB01 : B 0 1 = α⁻¹ * g 0 1 := by simp [hBdef]
  have hB10 : B 1 0 = α⁻¹ * g 1 0 := by simp [hBdef]
  have hB11 : B 1 1 = α⁻¹ * g 1 1 := by simp [hBdef]
  have hBdet : B.det * α ^ 2 = g 0 0 * g 1 1 - g 0 1 * g 1 0 := by
    rw [Matrix.det_fin_two, hB00, hB01, hB10, hB11]
    field_simp
  have hgα : g = !![α * B 0 0, α * B 0 1, 0; α * B 1 0, α * B 1 1, 0; 0, 0, α] := by
    rw [hg_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hB00, hB01, hB10, hB11, mul_inv_cancel_left₀ hα]
  have hB3 : B ^ 3 = 1 := uc22s2112r34_smul_cube hα hα3 hM3
  have hBbar : (B.map h.bar)ᵀ * B = 1 := by
    rw [hBdef]
    exact uc22s2112r34_unitary_smul_inv h hbarα' hMbar
  rcases uc22s2112r34_two_cases hB3 with ⟨μ', hμ'⟩ | hdet1 | ⟨hd1, u, w, hu, hw, hBu, hBw, hind⟩
  · refine Or.inr ⟨1, α * μ', α, by simp, ?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Matrix.one_apply]
    · rw [Matrix.mul_one, Matrix.one_mul, hgα]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hμ', Matrix.smul_apply]
  · refine Or.inl ⟨α, ?_⟩
    rw [hdetg, ← hBdet, hdet1]
    ring
  · have horth : h.bar (u 0) * w 0 + h.bar (u 1) * w 1 = 0 := by
      have hinter := uc22s2112r34_inner_pres h hBbar u w
      rw [hBu, hBw] at hinter
      simp only [Pi.smul_apply, smul_eq_mul] at hinter
      have hdne : B.det - 1 ≠ 0 := sub_ne_zero.mpr hd1
      have h : (B.det - 1) * (h.bar (u 0) * w 0 + h.bar (u 1) * w 1) = 0 := by
        linear_combination hinter
      exact (mul_eq_zero.mp h).resolve_left hdne
    have horth' : h.bar (w 0) * u 0 + h.bar (w 1) * u 1 = 0 := by
      have hh := congrArg h.bar horth
      simp only [map_add, map_mul, map_zero,
        CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_bar] at hh
      linear_combination hh
    have huu : h.bar (u 0) * u 0 + h.bar (u 1) * u 1 ≠ 0 := by
      intro h0
      have hX : h.bar (u 0) * (u 0 * w 1 - u 1 * w 0) = 0 := by
        linear_combination w 1 * h0 - u 1 * horth
      have hY : h.bar (u 1) * (u 0 * w 1 - u 1 * w 0) = 0 := by
        linear_combination -w 0 * h0 + u 0 * horth
      have h1 : h.bar (u 0) = 0 := (mul_eq_zero.mp hX).resolve_right hind
      have h2 : h.bar (u 1) = 0 := (mul_eq_zero.mp hY).resolve_right hind
      apply hu
      funext i
      fin_cases i
      · exact h.bar.injective (h1.trans (map_zero _).symm)
      · exact h.bar.injective (h2.trans (map_zero _).symm)
    have hww : h.bar (w 0) * w 0 + h.bar (w 1) * w 1 ≠ 0 := by
      intro h0
      have hdet' : w 0 * u 1 - w 1 * u 0 ≠ 0 := by
        intro hc
        apply hind
        linear_combination -hc
      have hX : h.bar (w 0) * (w 0 * u 1 - w 1 * u 0) = 0 := by
        linear_combination u 1 * h0 - w 1 * horth'
      have hY : h.bar (w 1) * (w 0 * u 1 - w 1 * u 0) = 0 := by
        linear_combination -u 0 * h0 + w 0 * horth'
      have h1 : h.bar (w 0) = 0 := (mul_eq_zero.mp hX).resolve_right hdet'
      have h2 : h.bar (w 1) = 0 := (mul_eq_zero.mp hY).resolve_right hdet'
      apply hw
      funext i
      fin_cases i
      · exact h.bar.injective (h1.trans (map_zero _).symm)
      · exact h.bar.injective (h2.trans (map_zero _).symm)
    have hbar_uu : h.bar (h.bar (u 0) * u 0 + h.bar (u 1) * u 1) =
        h.bar (u 0) * u 0 + h.bar (u 1) * u 1 := by
      simp [map_add, map_mul, CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_bar,
        mul_comm]
    obtain ⟨l, hl⟩ := h.normHom_surjective ⟨_, hbar_uu⟩
    have hnu : h.norm l = h.bar (u 0) * u 0 + h.bar (u 1) * u 1 := by
      have h2 := congrArg Subtype.val hl
      simpa [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.coe_normHom] using h2
    have hl0 : l ≠ 0 := by
      intro h0
      rw [h0] at hnu
      simp [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.norm] at hnu
      exact huu hnu.symm
    have hbar_ww : h.bar (h.bar (w 0) * w 0 + h.bar (w 1) * w 1) =
        h.bar (w 0) * w 0 + h.bar (w 1) * w 1 := by
      simp [map_add, map_mul, CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_bar,
        mul_comm]
    obtain ⟨l', hl'⟩ := h.normHom_surjective ⟨_, hbar_ww⟩
    have hnw : h.norm l' = h.bar (w 0) * w 0 + h.bar (w 1) * w 1 := by
      have h2 := congrArg Subtype.val hl'
      simpa [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.coe_normHom] using h2
    have hl'0 : l' ≠ 0 := by
      intro h0
      rw [h0] at hnw
      simp [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.norm] at hnw
      exact hww hnw.symm
    set u' : Fin 2 → K := l⁻¹ • u with hu'def
    set w' : Fin 2 → K := l'⁻¹ • w with hw'def
    have huu' : h.bar (u' 0) * u' 0 + h.bar (u' 1) * u' 1 = 1 := by
      have hnorm : l * h.bar l = h.bar (u 0) * u 0 + h.bar (u 1) * u 1 := by
        rw [← hnu]
        simp [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.norm]
      have hbl0 : h.bar l ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hnorm
        exact huu hnorm.symm
      have hne : h.bar l * l ≠ 0 := by
        rw [mul_comm (h.bar l) l, hnorm]
        exact huu
      have hkey : h.bar (u' 0) * u' 0 + h.bar (u' 1) * u' 1 =
          (h.bar l * l)⁻¹ * (h.bar (u 0) * u 0 + h.bar (u 1) * u 1) := by
        simp only [hu'def, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
        field_simp
      rw [hkey, ← hnorm, mul_comm l (h.bar l), inv_mul_cancel₀ hne]
    have hww' : h.bar (w' 0) * w' 0 + h.bar (w' 1) * w' 1 = 1 := by
      have hnorm : l' * h.bar l' = h.bar (w 0) * w 0 + h.bar (w 1) * w 1 := by
        rw [← hnw]
        simp [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.norm]
      have hbl0 : h.bar l' ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hnorm
        exact hww hnorm.symm
      have hne : h.bar l' * l' ≠ 0 := by
        rw [mul_comm (h.bar l') l', hnorm]
        exact hww
      have hkey : h.bar (w' 0) * w' 0 + h.bar (w' 1) * w' 1 =
          (h.bar l' * l')⁻¹ * (h.bar (w 0) * w 0 + h.bar (w 1) * w 1) := by
        simp only [hw'def, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
        field_simp
      rw [hkey, ← hnorm, mul_comm l' (h.bar l'), inv_mul_cancel₀ hne]
    have huw' : h.bar (u' 0) * w' 0 + h.bar (u' 1) * w' 1 = 0 := by
      have hkey : h.bar (u' 0) * w' 0 + h.bar (u' 1) * w' 1 =
          (h.bar l⁻¹ * l'⁻¹) * (h.bar (u 0) * w 0 + h.bar (u 1) * w 1) := by
        simp only [hu'def, hw'def, Pi.smul_apply, smul_eq_mul, map_mul]
        ring
      rw [hkey, horth, mul_zero]
    have huw'_sym : h.bar (w' 0) * u' 0 + h.bar (w' 1) * u' 1 = 0 := by
      have hh := congrArg h.bar huw'
      simp only [map_add, map_mul, map_zero,
        CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_bar] at hh
      linear_combination hh
    have hind' : u' 0 * w' 1 - u' 1 * w' 0 ≠ 0 := by
      have hkey : u' 0 * w' 1 - u' 1 * w' 0 =
          (l⁻¹ * l'⁻¹) * (u 0 * w 1 - u 1 * w 0) := by
        simp only [hu'def, hw'def, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hkey]
      exact mul_ne_zero (mul_ne_zero (inv_ne_zero hl0) (inv_ne_zero hl'0)) hind
    have hu'eig : B *ᵥ u' = u' := by
      rw [hu'def, Matrix.mulVec_smul, hBu]
    have hw'eig : B *ᵥ w' = B.det • w' := by
      rw [hw'def, Matrix.mulVec_smul, hBw, smul_smul, smul_smul, mul_comm]
    set P₀ : Matrix (Fin 3) (Fin 3) K :=
      !![u' 0, 0, w' 0; u' 1, 0, w' 1; 0, 1, 0] with hP₀
    have hP₀u : (P₀.map h.bar)ᵀ * P₀ = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hP₀, Matrix.mul_apply, Fin.sum_univ_three,
          Matrix.transpose_apply, Matrix.map_apply, huu', hww', huw', huw'_sym]
    have hδ : P₀.det = u' 1 * w' 0 - u' 0 * w' 1 := by
      rw [hP₀]
      simpa using uc22s2112r34_det_conj u' w' 1
    have hbarδ : h.bar (u' 1 * w' 0 - u' 0 * w' 1) * (u' 1 * w' 0 - u' 0 * w' 1) = 1 := by
      have hdet : (((P₀.map h.bar)ᵀ * P₀)).det = (1 : Matrix (Fin 3) (Fin 3) K).det := by
        rw [hP₀u]
      rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hdet
      have hmapdet : (P₀.map h.bar).det = h.bar P₀.det := by
        simpa using (RingHom.map_det h.bar P₀).symm
      rw [hmapdet, hδ] at hdet
      exact hdet
    have hδ0 : u' 1 * w' 0 - u' 0 * w' 1 ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hbarδ
      exact zero_ne_one hbarδ
    have hbark : (h.bar (u' 1 * w' 0 - u' 0 * w' 1))⁻¹ *
        (u' 1 * w' 0 - u' 0 * w' 1)⁻¹ = 1 := by
      simpa only [mul_inv, inv_one] using congrArg Inv.inv hbarδ
    set P : Matrix (Fin 3) (Fin 3) K :=
      !![u' 0, 0, (u' 1 * w' 0 - u' 0 * w' 1)⁻¹ * w' 0;
         u' 1, 0, (u' 1 * w' 0 - u' 0 * w' 1)⁻¹ * w' 1; 0, 1, 0] with hP
    have hPdet : P.det = 1 := by
      have h1 : P.det = (u' 1 * w' 0 - u' 0 * w' 1)⁻¹ * (u' 1 * w' 0 - u' 0 * w' 1) := by
        rw [hP]
        simpa using uc22s2112r34_det_conj u' w' (u' 1 * w' 0 - u' 0 * w' 1)⁻¹
      rw [h1]
      exact inv_mul_cancel₀ hδ0
    have hA : h.bar (u' 1) * h.bar (w' 0) - h.bar (u' 0) * h.bar (w' 1) =
        h.bar (u' 1 * w' 0 - u' 0 * w' 1) := by
      rw [map_sub, map_mul, map_mul]
    have hPu : (P.map h.bar)ᵀ * P = 1 := by
      have h02' : h.bar (u' 0) * ((u' 1 * w' 0 - u' 0 * w' 1)⁻¹ * w' 0) +
          h.bar (u' 1) * ((u' 1 * w' 0 - u' 0 * w' 1)⁻¹ * w' 1) = 0 := by
        rw [show h.bar (u' 0) * ((u' 1 * w' 0 - u' 0 * w' 1)⁻¹ * w' 0) +
            h.bar (u' 1) * ((u' 1 * w' 0 - u' 0 * w' 1)⁻¹ * w' 1) =
            (u' 1 * w' 0 - u' 0 * w' 1)⁻¹ *
              (h.bar (u' 0) * w' 0 + h.bar (u' 1) * w' 1) by ring]
        rw [huw', mul_zero]
      have h20' : (h.bar (u' 1) * h.bar (w' 0) - h.bar (u' 0) * h.bar (w' 1))⁻¹ *
            h.bar (w' 0) * u' 0 +
          (h.bar (u' 1) * h.bar (w' 0) - h.bar (u' 0) * h.bar (w' 1))⁻¹ * h.bar (w' 1) * u' 1 =
          0 := by
        rw [show (h.bar (u' 1) * h.bar (w' 0) - h.bar (u' 0) * h.bar (w' 1))⁻¹ *
              h.bar (w' 0) * u' 0 +
            (h.bar (u' 1) * h.bar (w' 0) - h.bar (u' 0) * h.bar (w' 1))⁻¹ *
              h.bar (w' 1) * u' 1 =
            (h.bar (u' 1) * h.bar (w' 0) - h.bar (u' 0) * h.bar (w' 1))⁻¹ *
              (h.bar (w' 0) * u' 0 + h.bar (w' 1) * u' 1) by ring]
        rw [huw'_sym, mul_zero]
      have h22' : (h.bar (u' 1) * h.bar (w' 0) - h.bar (u' 0) * h.bar (w' 1))⁻¹ *
            h.bar (w' 0) * ((u' 1 * w' 0 - u' 0 * w' 1)⁻¹ * w' 0) +
          (h.bar (u' 1) * h.bar (w' 0) - h.bar (u' 0) * h.bar (w' 1))⁻¹ * h.bar (w' 1) *
            ((u' 1 * w' 0 - u' 0 * w' 1)⁻¹ * w' 1) = 1 := by
        rw [show (h.bar (u' 1) * h.bar (w' 0) - h.bar (u' 0) * h.bar (w' 1))⁻¹ *
              h.bar (w' 0) * ((u' 1 * w' 0 - u' 0 * w' 1)⁻¹ * w' 0) +
            (h.bar (u' 1) * h.bar (w' 0) - h.bar (u' 0) * h.bar (w' 1))⁻¹ * h.bar (w' 1) *
              ((u' 1 * w' 0 - u' 0 * w' 1)⁻¹ * w' 1) =
            ((h.bar (u' 1) * h.bar (w' 0) - h.bar (u' 0) * h.bar (w' 1))⁻¹ *
              (u' 1 * w' 0 - u' 0 * w' 1)⁻¹) *
              (h.bar (w' 0) * w' 0 + h.bar (w' 1) * w' 1) by ring]
        rw [hww', mul_one, hA]
        exact hbark
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hP, Matrix.mul_apply, Fin.sum_univ_three,
          Matrix.transpose_apply, Matrix.map_apply, huu']
      all_goals first
        | exact h02'
        | exact h20'
        | exact h22'
    have hconj : g * P = P * Matrix.diagonal ![α, α, α * B.det] := by
      rw [hgα, hP]
      exact uc22s2112r34_conj_diag hu'eig hw'eig
    exact Or.inr ⟨P, α, α * B.det, hPdet, hPu, hconj⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
