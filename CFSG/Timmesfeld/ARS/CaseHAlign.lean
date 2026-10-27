module

public import CFSG.Timmesfeld.RankOne.SL2
public import Mathlib.RingTheory.PiTensorProduct

public section

namespace CFSG.Timmesfeld.ARS.CaseH

open CFSG.Timmesfeld CFSG.Timmesfeld.RankOne Matrix

variable {E : Type*} [Field E]

@[expose] def mElt [CharP E 2] (a : E) (ha : a ≠ 0) : SpecialLinearGroup (Fin 2) E :=
  ⟨!![0, a; a⁻¹, 0], by
    rw [det_fin_two_of]
    simp only [zero_mul, zero_sub, mul_inv_cancel₀ ha]
    exact CharTwo.neg_eq 1⟩

theorem val_upperElt (b : E) : (upperElt E b).1 = !![1, b; 0, 1] := rfl

theorem val_lowerElt (b : E) : (lowerElt E b).1 = !![1, 0; b, 1] := rfl

theorem val_mElt [CharP E 2] (a : E) (ha : a ≠ 0) : (mElt a ha).1 = !![0, a; a⁻¹, 0] := rfl

theorem val_mul (x y : SpecialLinearGroup (Fin 2) E) : (x * y).1 = x.1 * y.1 := rfl

theorem upperElt_mul_lowerElt_mul_upperElt [CharP E 2] (b c : E) :
    (upperElt E b * lowerElt E c * upperElt E b).1 = !![1 + b * c, b * b * c; c, 1 + b * c] := by
  rw [val_mul, val_mul, val_upperElt, val_lowerElt, Matrix.mul_fin_two, Matrix.mul_fin_two]
  congr 1
  ring_nf
  simp [CharTwo.two_eq_zero]

theorem upperElt_mul_lowerElt_inv_mul_upperElt [CharP E 2] (a : E) (ha : a ≠ 0) :
    upperElt E a * lowerElt E a⁻¹ * upperElt E a = mElt a ha := by
  apply Subtype.ext
  rw [upperElt_mul_lowerElt_mul_upperElt, val_mElt, mul_inv_cancel₀ ha, mul_assoc,
    mul_inv_cancel₀ ha, mul_one, CharTwo.add_self_eq_zero]

theorem mElt_mul_self [CharP E 2] (a : E) (ha : a ≠ 0) : mElt a ha * mElt a ha = 1 := by
  apply Subtype.ext
  rw [val_mul, val_mElt, Matrix.mul_fin_two]
  show _ = (1 : Matrix (Fin 2) (Fin 2) E)
  rw [Matrix.one_fin_two]
  congr 1
  simp [ha]

theorem mElt_conj_upperElt [CharP E 2] (a : E) (ha : a ≠ 0) (r : E) :
    mElt a ha * upperElt E r * (mElt a ha)⁻¹ = lowerElt E (a⁻¹ * a⁻¹ * r) := by
  have hinv : (mElt a ha)⁻¹ = mElt a ha := inv_eq_of_mul_eq_one_right (mElt_mul_self a ha)
  rw [hinv]
  apply Subtype.ext
  rw [val_mul, val_mul, val_mElt, val_upperElt, val_lowerElt, Matrix.mul_fin_two,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [ha]; try ring)

theorem entry_eq_zero_of_conj (x : SpecialLinearGroup (Fin 2) E) {c d : E} (hc : c ≠ 0)
    (h : x * upperElt E c * x⁻¹ = lowerElt E d) : x.1 0 0 = 0 := by
  have h' : x * upperElt E c = lowerElt E d * x := by rw [← h]; group
  have e := congrArg (fun g : SpecialLinearGroup (Fin 2) E => g.1 0 1) h'
  simp only [val_mul, val_upperElt, val_lowerElt] at e
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e
  rcases e with e | e
  · exact e
  · exact absurd e hc

theorem exists_aligned_SL2 [Finite E] [CharP E 2] (α : SpecialLinearGroup (Fin 2) E ≃*
      SpecialLinearGroup (Fin 2) E)
    (hU : ∀ s, ∃ t, α (upperElt E s) = upperElt E t)
    (hL : ∀ s, ∃ t, α (lowerElt E s) = lowerElt E t) :
    ∃ (ε : E) (σ : E ≃+* E), ε ≠ 0 ∧ (∀ s, α (upperElt E s) = upperElt E (ε * σ s)) ∧
      ∀ s, α (lowerElt E s) = lowerElt E (ε⁻¹ * σ s) := by
  classical
  choose f hf using hU
  choose g hg using hL
  have hfadd : ∀ s t, f (s + t) = f s + f t := fun s t => upperElt_injective E (by
    rw [← hf, ← upperElt_mul, ← upperElt_mul, map_mul, hf, hf])
  have hgadd : ∀ s t, g (s + t) = g s + g t := fun s t => lowerElt_injective E (by
    rw [← hg, ← lowerElt_mul, ← lowerElt_mul, map_mul, hg, hg])
  have hfinj : Function.Injective f := fun s t e => upperElt_injective E
    (α.injective (by rw [hf, hf, e]))
  have hf0 : f 0 = 0 := by
    have := hfadd 0 0
    simp only [add_zero] at this
    exact left_eq_add.mp this
  have hfne : ∀ a, a ≠ 0 → f a ≠ 0 := fun a ha e => ha (hfinj (e.trans hf0.symm))
  have hm : ∀ a (ha : a ≠ 0), g a⁻¹ = (f a)⁻¹ ∧ α (mElt a ha) = mElt (f a) (hfne a ha) := by
    intro a ha
    have hx : α (mElt a ha) = upperElt E (f a) * lowerElt E (g a⁻¹) * upperElt E (f a) := by
      rw [← upperElt_mul_lowerElt_inv_mul_upperElt a ha, map_mul, map_mul, hf, hg]
    have hconj := congrArg α (mElt_conj_upperElt a ha 1)
    rw [map_mul, map_mul, map_inv, hf, hg] at hconj
    have h00 := entry_eq_zero_of_conj _ (hfne 1 one_ne_zero) hconj
    rw [hx, upperElt_mul_lowerElt_mul_upperElt] at h00
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
      Matrix.cons_val_fin_one] at h00
    have h1 : f a * g a⁻¹ = 1 := by
      have := congrArg (· + 1) h00
      simp only [zero_add] at this
      rw [add_comm, ← add_assoc, CharTwo.add_self_eq_zero, zero_add] at this
      exact this
    have hg' : g a⁻¹ = (f a)⁻¹ := eq_inv_of_mul_eq_one_right h1
    refine ⟨hg', ?_⟩
    rw [hx, hg', upperElt_mul_lowerElt_inv_mul_upperElt]
  have hkey : ∀ a, a ≠ 0 → ∀ r, g (a⁻¹ * a⁻¹ * r) = (f a)⁻¹ * (f a)⁻¹ * f r := by
    intro a ha r
    have hconj := congrArg α (mElt_conj_upperElt a ha r)
    rw [map_mul, map_mul, map_inv, hf, hg, (hm a ha).2, mElt_conj_upperElt] at hconj
    exact (lowerElt_injective E hconj).symm
  set ε := f 1 with hε
  have hε0 : ε ≠ 0 := hfne 1 one_ne_zero
  have hgf : ∀ b, g b = ε⁻¹ * ε⁻¹ * f b := fun b => by
    have := hkey 1 one_ne_zero b
    rwa [inv_one, one_mul, one_mul] at this
  have hsq : ∀ a b, f (a * a * b) = f a * f a * (ε⁻¹ * ε⁻¹ * f b) := by
    intro a b
    by_cases ha : a = 0
    · rw [ha, zero_mul, zero_mul, hf0, zero_mul, zero_mul]
    · have := hkey a ha (a * a * b)
      rw [show a⁻¹ * a⁻¹ * (a * a * b) = b by field_simp, hgf] at this
      have hfa := hfne a ha
      field_simp at this ⊢
      linear_combination -this
  let σf : E → E := fun x => ε⁻¹ * f x
  have hσ1 : σf 1 = 1 := by simp only [σf, ← hε, inv_mul_cancel₀ hε0]
  have hσsq : ∀ a b, σf (a * a * b) = σf a * σf a * σf b := by
    intro a b
    simp only [σf, hsq]
    ring
  have hσmul : ∀ x y, σf (x * y) = σf x * σf y := by
    intro x y
    obtain ⟨a, rfl⟩ := FiniteField.isSquare_of_char_two (ringChar.eq E 2) x
    rw [hσsq, show σf (a * a) = σf a * σf a by
      have := hσsq a 1
      rwa [mul_one, hσ1, mul_one] at this]
  have hσadd : ∀ x y, σf (x + y) = σf x + σf y := fun x y => by
    simp only [σf, hfadd, mul_add]
  have hσinj : Function.Injective σf := fun x y e =>
    hfinj (mul_left_cancel₀ (inv_ne_zero hε0) e)
  let σh : E →+* E :=
    { toFun := σf
      map_one' := hσ1
      map_mul' := hσmul
      map_zero' := by simp only [σf, hf0, mul_zero]
      map_add' := hσadd }
  let σ : E ≃+* E := RingEquiv.ofBijective σh (Finite.injective_iff_bijective.mp hσinj)
  refine ⟨ε, σ, hε0, fun s => ?_, fun s => ?_⟩
  · rw [hf]
    congr 1
    change f s = ε * (ε⁻¹ * f s)
    rw [← mul_assoc, mul_inv_cancel₀ hε0, one_mul]
  · rw [hg, hgf]
    congr 1
    change ε⁻¹ * ε⁻¹ * f s = ε⁻¹ * (ε⁻¹ * f s)
    ring

end CFSG.Timmesfeld.ARS.CaseH
