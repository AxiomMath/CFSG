module

public import CFSG.Quasithin.Vol2.Ch11SecS12O

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F] [CharP F 2]

theorem exists_diag_two {B : Matrix (Fin 2) (Fin 2) F} (h3 : B * B * B = 1)
    (hns : ¬ (B 0 1 = 0 ∧ B 1 0 = 0 ∧ B 0 0 = B 1 1)) {ω : F} (hω : ω ^ 2 + ω + 1 = 0) :
    ∃ P : Matrix (Fin 2) (Fin 2) F, P.det ≠ 0 ∧ ∃ β₁ β₂ : F, B * P = P * diagonal ![β₁, β₂] := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have e : ∀ i j, (B * B * B) i j = (1 : Matrix (Fin 2) (Fin 2) F) i j := fun i j => by rw [h3]
  have E00 := e 0 0
  have E01 := e 0 1
  have E10 := e 1 0
  have E11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at E00 E01 E10 E11
  obtain ⟨t, ht⟩ : ∃ t : F, t = B 0 0 + B 1 1 := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : F, δ = B 0 0 * B 1 1 - B 0 1 * B 1 0 := ⟨_, rfl⟩
  have hq : B 0 1 * (t ^ 2 - δ) = 0 := by
    linear_combination E01 + B 0 1 * (t + B 0 0 + B 1 1) * ht - B 0 1 * hδ
  have hr : B 1 0 * (t ^ 2 - δ) = 0 := by
    linear_combination E10 + B 1 0 * (t + B 0 0 + B 1 1) * ht - B 1 0 * hδ
  have hp : B 0 0 * (t ^ 2 - δ) - t * δ = 1 := by
    linear_combination E00 + (B 0 0 * (t + B 0 0 + B 1 1) - δ) * ht - (2 * B 0 0 + B 1 1) * hδ
  have hs : B 1 1 * (t ^ 2 - δ) - t * δ = 1 := by
    linear_combination E11 + (B 1 1 * (t + B 0 0 + B 1 1) - δ) * ht - (B 0 0 + 2 * B 1 1) * hδ
  have hδt : δ = t ^ 2 := by
    by_contra hne
    have h0 : t ^ 2 - δ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    apply hns
    refine ⟨(mul_eq_zero.mp hq).resolve_right h0, (mul_eq_zero.mp hr).resolve_right h0, ?_⟩
    have : (B 0 0 - B 1 1) * (t ^ 2 - δ) = 0 := by linear_combination hp - hs
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h0)
  have ht3 : t ^ 3 = 1 := by
    rw [hδt] at hp
    linear_combination -hp - h2
  have ht0 : t ≠ 0 := by
    rintro h
    rw [h] at ht3
    norm_num at ht3
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hωω : ω ≠ ω ^ 2 := by
    intro h
    have : ω * (ω - 1) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp this with h0 | h0
    · rw [h0] at hω
      norm_num at hω
    · have h1 : ω = 1 := sub_eq_zero.mp h0
      rw [h1] at hω
      have : (1 : F) = 0 := by linear_combination hω - h2
      exact one_ne_zero this
  have hev : ∀ β : F, β ^ 2 + t * β + t ^ 2 = 0 →
      ∃ v : Fin 2 → F, v ≠ 0 ∧ B *ᵥ v = β • v := by
    intro β hβ
    have hdet : (B - β • (1 : Matrix (Fin 2) (Fin 2) F)).det = 0 := by
      rw [Matrix.det_fin_two]
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
        Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
        Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), mul_zero, sub_zero]
      linear_combination hβ - t * β * h2 + hδt + β * ht - hδ
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    refine ⟨v, hv0, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
    exact hv
  obtain ⟨v₁, hv₁0, hv₁⟩ := hev (t * ω) (by linear_combination t ^ 2 * hω)
  obtain ⟨v₂, hv₂0, hv₂⟩ := hev (t * ω ^ 2)
    (by linear_combination t ^ 2 * hω + t ^ 2 * ω * hω3)
  refine ⟨!![v₁ 0, v₂ 0; v₁ 1, v₂ 1], ?_, t * ω, t * ω ^ 2, ?_⟩
  · intro hdet
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hx' : ∀ i, x 0 * v₁ i + x 1 * v₂ i = 0 := fun i => by
      have := congrFun hx i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this ⊢ <;>
        linear_combination this
    have hBx : ∀ i, x 0 * (t * ω) * v₁ i + x 1 * (t * ω ^ 2) * v₂ i = 0 := fun i => by
      have h1 := congrFun hv₁ i
      have h2' := congrFun hv₂ i
      have h3 : (B *ᵥ fun j => x 0 * v₁ j + x 1 * v₂ j) i = 0 := by
        have : (fun j => x 0 * v₁ j + x 1 * v₂ j) = 0 := funext hx'
        rw [this, Matrix.mulVec_zero]
        rfl
      have h4 : (B *ᵥ fun j => x 0 * v₁ j + x 1 * v₂ j) =
          x 0 • (B *ᵥ v₁) + x 1 • (B *ᵥ v₂) := by
        rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_add]
        rfl
      rw [h4, hv₁, hv₂] at h3
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h3
      linear_combination h3
    have hdiff : t * (ω - ω ^ 2) ≠ 0 := mul_ne_zero ht0 (sub_ne_zero.mpr hωω)
    have hx0' : x 0 = 0 := by
      by_contra hne
      apply hv₁0
      funext i
      have : x 0 * (t * (ω - ω ^ 2)) * v₁ i = 0 := by
        linear_combination hBx i - t * ω ^ 2 * hx' i
      simpa [hne, hdiff] using this
    have hx1 : x 1 = 0 := by
      by_contra hne
      apply hv₂0
      funext i
      have := hx' i
      rw [hx0', zero_mul, zero_add] at this
      simpa [hne] using this
    apply hx0
    funext i
    fin_cases i
    · exact hx0'
    · exact hx1
  · ext i j
    have h1 := congrFun hv₁ i
    have h2' := congrFun hv₂ i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at h1 h2'
    rw [Matrix.mul_diagonal, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp at h1 h2' ⊢ <;>
      first | linear_combination h1 | linear_combination h2'

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
