module

public import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalDefs

import CFSG.Quasithin.Recognition.St84.Gen.SL2Semilinear

public section

namespace CFSG.Quasithin.F112R.St84

open scoped MatrixGroups

variable {F : Type*} [Field F]

section Matrices

private theorem G2q.squareMap_radMat_twist [CharP F 2] (A : SL(2, F)) (β : Fin 2 → F) :
    (sp4RadMat A).mulVec ![0, β 0 ^ 2, β 1 ^ 2] =
      ![A 1 0 * A 0 0 * β 0 ^ 2 + A 1 1 * A 0 1 * β 1 ^ 2,
        ((A : Matrix (Fin 2) (Fin 2) F).mulVec β) 0 ^ 2,
        ((A : Matrix (Fin 2) (Fin 2) F).mulVec β) 1 ^ 2] := by
  rw [sp4RadMat_mulVec]
  ext i; fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, CharTwo.add_sq, mul_pow]

private theorem G2q.squareMap_radMat_axis (A : SL(2, F)) (x : F) :
    (sp4RadMat A).mulVec ![x, 0, 0] = ![x, 0, 0] := by
  rw [sp4RadMat_mulVec]
  simp

end Matrices

section Equivariance

variable {s : (Fin 3 → F) → (Fin 2 → F)}
  (hM : ∀ (M : SL(2, F)) (v : Fin 3 → F),
    s ((sp4RadMat M).mulVec v) = (M : Matrix (Fin 2) (Fin 2) F).mulVec (s v))
include hM

private theorem G2q.squareMap_apply (M : SL(2, F)) (x y₁ y₂ : F) :
    s ![x + M 1 0 * M 0 0 * y₁ + M 1 1 * M 0 1 * y₂, M 0 0 ^ 2 * y₁ + M 0 1 ^ 2 * y₂,
        M 1 0 ^ 2 * y₁ + M 1 1 ^ 2 * y₂] =
      ![M 0 0 * s ![x, y₁, y₂] 0 + M 0 1 * s ![x, y₁, y₂] 1,
        M 1 0 * s ![x, y₁, y₂] 0 + M 1 1 * s ![x, y₁, y₂] 1] := by
  have h := hM M ![x, y₁, y₂]
  rw [sp4RadMat_mulVec] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h
  rw [h]
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem G2q.squareMap_unip (t x y₁ y₂ : F) :
    s ![x + t * y₂, y₁ + t ^ 2 * y₂, y₂] =
      ![s ![x, y₁, y₂] 0 + t * s ![x, y₁, y₂] 1, s ![x, y₁, y₂] 1] := by
  simpa using G2q.squareMap_apply hM ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩ x y₁ y₂

private theorem G2q.squareMap_lowr (t x y₁ y₂ : F) :
    s ![x + t * y₁, y₁, t ^ 2 * y₁ + y₂] =
      ![s ![x, y₁, y₂] 0, t * s ![x, y₁, y₂] 0 + s ![x, y₁, y₂] 1] := by
  simpa using G2q.squareMap_apply hM ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩ x y₁ y₂

private theorem G2q.squareMap_torus {μ : F} (hμ : μ ≠ 0) (x y₁ y₂ : F) :
    s ![x, μ ^ 2 * y₁, μ⁻¹ ^ 2 * y₂] =
      ![μ * s ![x, y₁, y₂] 0, μ⁻¹ * s ![x, y₁, y₂] 1] := by
  simpa using
    G2q.squareMap_apply hM ⟨!![μ, 0; 0, μ⁻¹], by simp [Matrix.det_fin_two, hμ]⟩ x y₁ y₂

private theorem G2q.squareMap_weyl [CharP F 2] (x y₁ y₂ : F) :
    s ![x, y₂, y₁] = ![s ![x, y₁, y₂] 1, s ![x, y₁, y₂] 0] := by
  simpa using G2q.squareMap_apply hM
    ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩ x y₁ y₂

private theorem G2q.squareMap_axis (x : F) : s ![x, 0, 0] = 0 := by
  have h1 := congrFun (G2q.squareMap_unip hM 1 x 0 0) 0
  have h2 := congrFun (G2q.squareMap_lowr hM 1 x 0 0) 1
  simp at h1 h2
  ext i; fin_cases i <;> simp [h1, h2]

private theorem G2q.squareMap_low (b : F) : s ![0, 0, b ^ 2] = ![0, b * s ![0, 0, 1] 1] := by
  have ha : s ![0, 0, 1] 0 = 0 := by simpa using congrFun (G2q.squareMap_lowr hM 1 0 0 1) 1
  by_cases hb : b = 0
  · subst hb
    ext i; fin_cases i <;> simp [G2q.squareMap_axis hM 0]
  · simpa [ha] using G2q.squareMap_torus hM (inv_ne_zero hb) 0 0 1

end Equivariance

section Polarization

variable {s : (Fin 3 → F) → (Fin 2 → F)} {P : (Fin 3 → F) → (Fin 3 → F) → (Fin 2 → F)}
  (hpol : ∀ v w, s (v + w) = s v + s w + P v w)
  (hM : ∀ (M : SL(2, F)) (v : Fin 3 → F),
    s ((sp4RadMat M).mulVec v) = (M : Matrix (Fin 2) (Fin 2) F).mulVec (s v))
include hpol hM

private theorem G2q.squareMap_P_equiv (M : SL(2, F)) (v w : Fin 3 → F) :
    P ((sp4RadMat M).mulVec v) ((sp4RadMat M).mulVec w) =
      (M : Matrix (Fin 2) (Fin 2) F).mulVec (P v w) := by
  have h1 := hM M (v + w)
  rw [Matrix.mulVec_add, hpol ((sp4RadMat M).mulVec v) ((sp4RadMat M).mulVec w), hM M v, hM M w,
    hpol v w, Matrix.mulVec_add, Matrix.mulVec_add] at h1
  exact add_left_cancel h1

private theorem G2q.squareMap_P_axis (x x' : F) : P ![x, 0, 0] ![x', 0, 0] = 0 := by
  have h := hpol ![x, 0, 0] ![x', 0, 0]
  have e : (![x, 0, 0] + ![x', 0, 0] : Fin 3 → F) = ![x + x', 0, 0] := by
    ext i; fin_cases i <;> simp
  rw [e, G2q.squareMap_axis hM, G2q.squareMap_axis hM, G2q.squareMap_axis hM] at h
  simpa using h.symm

private theorem G2q.squareMap_exists_smul [CharP F 2]
    (hP₂ : ∀ u v w, P u (v + w) = P u v + P u w) (x : F) :
    ∃ z : F, ∀ β : Fin 2 → F, P ![x, 0, 0] ![0, β 0 ^ 2, β 1 ^ 2] = z • β := by
  let E : (Fin 2 → F) →+ (Fin 2 → F) :=
    AddMonoidHom.mk' (fun β => P ![x, 0, 0] ![0, β 0 ^ 2, β 1 ^ 2]) fun β γ => by
      have e : (![0, (β + γ) 0 ^ 2, (β + γ) 1 ^ 2] : Fin 3 → F) =
          ![0, β 0 ^ 2, β 1 ^ 2] + ![0, γ 0 ^ 2, γ 1 ^ 2] := by
        ext i; fin_cases i <;> simp [CharTwo.add_sq]
      simp only [e, hP₂]
  obtain ⟨z, hz⟩ := exists_eq_smul_of_commute_SL2 E fun A β => by
    show P ![x, 0, 0] ![0, ((A : Matrix (Fin 2) (Fin 2) F).mulVec β) 0 ^ 2,
        ((A : Matrix (Fin 2) (Fin 2) F).mulVec β) 1 ^ 2] =
      (A : Matrix (Fin 2) (Fin 2) F).mulVec (P ![x, 0, 0] ![0, β 0 ^ 2, β 1 ^ 2])
    have h := G2q.squareMap_P_equiv hpol hM A ![x, 0, 0] ![0, β 0 ^ 2, β 1 ^ 2]
    rw [G2q.squareMap_radMat_twist, G2q.squareMap_radMat_axis] at h
    have e : (![A 1 0 * A 0 0 * β 0 ^ 2 + A 1 1 * A 0 1 * β 1 ^ 2,
        ((A : Matrix (Fin 2) (Fin 2) F).mulVec β) 0 ^ 2,
        ((A : Matrix (Fin 2) (Fin 2) F).mulVec β) 1 ^ 2] : Fin 3 → F) =
        ![A 1 0 * A 0 0 * β 0 ^ 2 + A 1 1 * A 0 1 * β 1 ^ 2, 0, 0] +
        ![0, ((A : Matrix (Fin 2) (Fin 2) F).mulVec β) 0 ^ 2,
          ((A : Matrix (Fin 2) (Fin 2) F).mulVec β) 1 ^ 2] := by
      ext i; fin_cases i <;> simp
    rw [e, hP₂, G2q.squareMap_P_axis hpol hM, zero_add] at h
    exact h
  exact ⟨z, hz⟩

private theorem G2q.squareMap_exists_c [CharP F 2]
    (hP₁ : ∀ u v w, P (u + v) w = P u w + P v w)
    (hP₂ : ∀ u v w, P u (v + w) = P u v + P u w) :
    ∃ c : F → F, (∀ x x' b₀ b₁ : F, P ![x, 0, 0] ![x', b₀ ^ 2, b₁ ^ 2] = c x • ![b₀, b₁]) ∧
      ∀ x x' : F, c (x + x') = c x + c x' := by
  choose c hc using G2q.squareMap_exists_smul hpol hM hP₂
  have hcP : ∀ x x' b₀ b₁ : F, P ![x, 0, 0] ![x', b₀ ^ 2, b₁ ^ 2] = c x • ![b₀, b₁] := by
    intro x x' b₀ b₁
    have e : (![x', b₀ ^ 2, b₁ ^ 2] : Fin 3 → F) = ![x', 0, 0] + ![0, b₀ ^ 2, b₁ ^ 2] := by
      ext i; fin_cases i <;> simp
    rw [e, hP₂, G2q.squareMap_P_axis hpol hM, zero_add]
    simpa using hc x ![b₀, b₁]
  refine ⟨c, hcP, fun x x' => ?_⟩
  have e : (![x, 0, 0] + ![x', 0, 0] : Fin 3 → F) = ![x + x', 0, 0] := by
    ext i; fin_cases i <;> simp
  have h := hP₁ ![x, 0, 0] ![x', 0, 0] ![0, 1 ^ 2, 0 ^ 2]
  rw [e, hcP, hcP, hcP] at h
  simpa using congrFun h 0

private theorem G2q.squareMap_formula_ne [CharP F 2] {c : F → F}
    (hcP : ∀ x x' b₀ b₁ : F, P ![x, 0, 0] ![x', b₀ ^ 2, b₁ ^ 2] = c x • ![b₀, b₁])
    {b₁ : F} (hb₁ : b₁ ≠ 0) (b₀ : F) :
    s ![0, b₀ ^ 2, b₁ ^ 2] = (s ![0, 0, 1] 1 + c (b₀ * b₁)) • ![b₀, b₁] := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have ht : b₀ / b₁ * b₁ = b₀ := div_mul_cancel₀ b₀ hb₁
  have e1 := G2q.squareMap_unip hM (b₀ / b₁) 0 0 (b₁ ^ 2)
  rw [G2q.squareMap_low hM b₁] at e1
  have e2 : (![0 + b₀ / b₁ * b₁ ^ 2, 0 + (b₀ / b₁) ^ 2 * b₁ ^ 2, b₁ ^ 2] : Fin 3 → F) =
      ![b₀ * b₁, 0, 0] + ![0, b₀ ^ 2, b₁ ^ 2] := by
    ext i; fin_cases i
    · simp; linear_combination b₁ * ht
    · simp; linear_combination (b₀ / b₁ * b₁ + b₀) * ht
    · simp
  rw [e2, hpol, G2q.squareMap_axis hM, hcP, zero_add] at e1
  ext i; fin_cases i
  · have h := congrFun e1 0
    simp at h ⊢
    linear_combination h - (c (b₀ * b₁) * b₀) * h2 + (s ![0, 0, 1] 1) * ht
  · have h := congrFun e1 1
    simp at h ⊢
    linear_combination h - (c (b₀ * b₁) * b₁) * h2

private theorem G2q.squareMap_formula [CharP F 2] {c : F → F}
    (hcP : ∀ x x' b₀ b₁ : F, P ![x, 0, 0] ![x', b₀ ^ 2, b₁ ^ 2] = c x • ![b₀, b₁])
    (hcadd : ∀ x x' : F, c (x + x') = c x + c x') (x b₀ b₁ : F) :
    s ![x, b₀ ^ 2, b₁ ^ 2] = (s ![0, 0, 1] 1 + c x + c (b₀ * b₁)) • ![b₀, b₁] := by
  have hc0 : c 0 = 0 := by simpa using hcadd 0 0
  have h0 : s ![0, b₀ ^ 2, b₁ ^ 2] = (s ![0, 0, 1] 1 + c (b₀ * b₁)) • ![b₀, b₁] := by
    by_cases hb₁ : b₁ = 0
    · subst hb₁
      have h := G2q.squareMap_weyl hM 0 0 (b₀ ^ 2)
      rw [G2q.squareMap_low hM b₀] at h
      ext i; fin_cases i <;> simp [hc0] at h ⊢ <;> simp [h] <;> ring
    · exact G2q.squareMap_formula_ne hpol hM hcP hb₁ b₀
  have e : (![x, b₀ ^ 2, b₁ ^ 2] : Fin 3 → F) = ![x, 0, 0] + ![0, b₀ ^ 2, b₁ ^ 2] := by
    ext i; fin_cases i <;> simp
  rw [e, hpol, G2q.squareMap_axis hM, hcP, h0, zero_add, ← add_smul]
  congr 1
  ring

end Polarization

section Conclusion

variable {s : (Fin 3 → F) → (Fin 2 → F)} {P : (Fin 3 → F) → (Fin 3 → F) → (Fin 2 → F)}

private theorem G2q.squareMap_linear [CharP F 2]
    (hpol : ∀ v w, s (v + w) = s v + s w + P v w)
    (hP₁ : ∀ u v w, P (u + v) w = P u w + P v w) {c : F → F} {k : F}
    (hcadd : ∀ x x' : F, c (x + x') = c x + c x')
    (hform : ∀ x b₀ b₁ : F, s ![x, b₀ ^ 2, b₁ ^ 2] = (k + c x + c (b₀ * b₁)) • ![b₀, b₁])
    (b : F) : c b = c 1 * b := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hc0 : c 0 = 0 := by simpa using hcadd 0 0
  have pe : ∀ b₀ : F, P ![0, b₀ ^ 2, 0] ![0, 0, 1] = c b₀ • ![b₀, 1] := by
    intro b₀
    have e : (![0, b₀ ^ 2, 0] + ![0, 0, 1] : Fin 3 → F) = ![0, b₀ ^ 2, 1 ^ 2] := by
      ext i; fin_cases i <;> simp
    have h1 := hpol ![0, b₀ ^ 2, 0] ![0, 0, 1]
    have h3 : s ![0, b₀ ^ 2, 0] = (k + c 0 + c (b₀ * 0)) • ![b₀, 0] := by
      simpa using hform 0 b₀ 0
    have h4 : s ![0, 0, 1] = (k + c 0 + c (0 * 1)) • ![0, 1] := by
      simpa using hform 0 0 1
    rw [e, hform 0 b₀ 1, h3, h4] at h1
    ext i; fin_cases i
    · have := congrFun h1 0
      simp [hc0] at this ⊢
      linear_combination -this
    · have := congrFun h1 1
      simp [hc0] at this ⊢
      linear_combination -this
  have e : (![0, (b + 1) ^ 2, 0] : Fin 3 → F) = ![0, b ^ 2, 0] + ![0, 1 ^ 2, 0] := by
    ext i; fin_cases i <;> simp [CharTwo.add_sq]
  have h1 := hP₁ ![0, b ^ 2, 0] ![0, 1 ^ 2, 0] ![0, 0, 1]
  rw [← e, pe, pe, pe, hcadd b 1] at h1
  have := congrFun h1 0
  simp at this
  linear_combination this - (c 1 * b) * h2

private theorem G2q.squareMap_weight [CharP F 2] {c₁ k l χ : F} (hl0 : l ≠ 0) (hl1 : l ≠ 1)
    (hc₁ : c₁ ≠ 0)
    (hform : ∀ x b₀ b₁ : F,
      s ![x, b₀ ^ 2, b₁ ^ 2] = (k + c₁ * x + c₁ * (b₀ * b₁)) • ![b₀, b₁])
    (hT : ∀ v, s (l ^ 2 • v) = χ • s v) : χ = l ^ 3 ∧ k = 0 := by
  have key : ∀ x : F, (k + c₁ * (l ^ 2 * x) + c₁ * (l * 0)) * l =
      χ * (k + c₁ * x + c₁ * (1 * 0)) := by
    intro x
    have h1 := hT ![x, 1 ^ 2, 0 ^ 2]
    have e : (l ^ 2 • ![x, 1 ^ 2, 0 ^ 2] : Fin 3 → F) = ![l ^ 2 * x, l ^ 2, 0 ^ 2] := by
      ext i; fin_cases i <;> simp
    rw [e, hform, hform] at h1
    simpa using congrFun h1 0
  have e0 := key 0
  have e1 := key 1
  have hχ : χ = l ^ 3 := by
    apply mul_left_cancel₀ hc₁
    linear_combination e0 - e1
  refine ⟨hχ, ?_⟩
  subst hχ
  have h1l : 1 - l ≠ 0 := sub_ne_zero.mpr (Ne.symm hl1)
  have h2l : 1 + l ≠ 0 := by
    intro h'
    apply hl1
    have : l = -1 := by linear_combination h'
    rw [this, CharTwo.neg_eq]
  have : k * (l * ((1 - l) * (1 + l))) = 0 := by linear_combination e0
  simpa [hl0, h1l, h2l] using this

end Conclusion

theorem G2q.exists_squareMap_eq [Finite F] [CharP F 2]
    (s : (Fin 3 → F) → (Fin 2 → F)) (P : (Fin 3 → F) → (Fin 3 → F) → (Fin 2 → F))
    (hpol : ∀ v w, s (v + w) = s v + s w + P v w)
    (hP₁ : ∀ u v w, P (u + v) w = P u w + P v w)
    (hP₂ : ∀ u v w, P u (v + w) = P u v + P u w)
    (hM : ∀ (M : SL(2, F)) (v : Fin 3 → F),
      s ((sp4RadMat M).mulVec v) = (M : Matrix (Fin 2) (Fin 2) F).mulVec (s v))
    {l χ : F} (hl0 : l ≠ 0) (hl1 : l ≠ 1) (hT : ∀ v, s (l ^ 2 • v) = χ • s v)
    (hnd : ∀ x : F, x ≠ 0 → ∃ v, P ![x, 0, 0] v ≠ 0) :
    ∃ c : F, c ≠ 0 ∧ χ = l ^ 3 ∧
      ∀ x b₀ b₁ : F, s ![x, b₀ ^ 2, b₁ ^ 2] = (c * (x + b₀ * b₁)) • ![b₀, b₁] := by
  obtain ⟨c, hcP, hcadd⟩ := G2q.squareMap_exists_c hpol hM hP₁ hP₂
  have hform := G2q.squareMap_formula hpol hM hcP hcadd
  have hlin := G2q.squareMap_linear hpol hP₁ hcadd hform
  have hform' : ∀ x b₀ b₁ : F, s ![x, b₀ ^ 2, b₁ ^ 2] =
      (s ![0, 0, 1] 1 + c 1 * x + c 1 * (b₀ * b₁)) • ![b₀, b₁] := by
    intro x b₀ b₁
    rw [hform, hlin x, hlin (b₀ * b₁)]
  have hc1 : c 1 ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := hnd 1 one_ne_zero
    apply hv
    obtain ⟨b₀, hb₀⟩ := isSquare_of_charTwo' (v 1)
    obtain ⟨b₁, hb₁⟩ := isSquare_of_charTwo' (v 2)
    have e : v = ![v 0, b₀ ^ 2, b₁ ^ 2] := by
      ext i; fin_cases i <;> simp [hb₀, hb₁, sq]
    rw [e, hcP, h0, zero_smul]
  obtain ⟨hχ, hk⟩ := G2q.squareMap_weight hl0 hl1 hc1 hform' hT
  refine ⟨c 1, hc1, hχ, fun x b₀ b₁ => ?_⟩
  rw [hform', hk, zero_add, ← mul_add]

end CFSG.Quasithin.F112R.St84

end
