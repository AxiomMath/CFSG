module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.Quasithin.SL3Small

open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem eq_sum_single (x : Fin 3 → F) :
    x = Pi.single 0 (x 0) + Pi.single 1 (x 1) + Pi.single 2 (x 2) := by
  ext l
  fin_cases l <;> simp

theorem exists_third {i j : Fin 3} (hij : i ≠ j) : ∃ k, k ≠ i ∧ k ≠ j := by
  fin_cases i <;> fin_cases j <;> simp at hij
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩

theorem diag2n_mulVec_single {i j : Fin 3} (hij : i ≠ j) {c : F} (hc : c ≠ 0) (l : Fin 3)
    (a : F) :
    ((SpecialLinearGroup.diag2n hij c hc : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        Pi.single l a =
      Pi.single l ((if l = i then c else if l = j then c⁻¹ else 1) * a) := by
  rw [SpecialLinearGroup.diag2n_coe, diagonal_mulVec_single]

theorem single_mulVec_single_self (i k : Fin 3) (a : F) :
    (single i k (1 : F)) *ᵥ (Pi.single k a : Fin 3 → F) = Pi.single i a := by
  ext l
  simp only [mulVec, dotProduct, single_apply, Pi.single_apply]
  by_cases hl : l = i
  · subst hl
    simp
  · simp [hl, Ne.symm hl]

theorem transvection_mulVec_single_self {i k : Fin 3} (hik : i ≠ k) (a : F) :
    ((SpecialLinearGroup.transvection hik (1 : F) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        Pi.single k a = Pi.single k a + Pi.single i a := by
  rw [SpecialLinearGroup.transvection_coe, add_mulVec, one_mulVec, single_mulVec_single_self]

section Biadd

variable {M : Type} [Group M] (B : (Fin 3 → F) → (Fin 3 → F) → M)
  (h1 : ∀ x x' y, B (x + x') y = B x y * B x' y) (h2 : ∀ x y y', B x (y + y') = B x y * B x y')
  (hinv : ∀ (g : SL(3, F)) x y,
    B ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ x) ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ y) = B x y)

include h1 hinv in
theorem biadd_single_ne {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) {i j : Fin 3} (hij : i ≠ j)
    (a b : F) : B (Pi.single i a) (Pi.single j b) = 1 := by
  obtain ⟨k, hki, hkj⟩ := exists_third hij
  have hik : i ≠ k := fun h => hki h.symm
  have hc' : c - 1 ≠ 0 := sub_ne_zero.mpr hc1
  have m1 : ((SpecialLinearGroup.diag2n hik c hc0 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (Pi.single i ((c - 1)⁻¹ * a) : Fin 3 → F) =
        Pi.single i ((c - 1)⁻¹ * a) + Pi.single i a := by
    rw [diag2n_mulVec_single, ← Pi.single_add]
    congr 1
    simp only [↓reduceIte]
    field_simp
    ring
  have m2 : ((SpecialLinearGroup.diag2n hik c hc0 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (Pi.single j b : Fin 3 → F) = Pi.single j b := by
    rw [diag2n_mulVec_single]
    simp only [Ne.symm hij, Ne.symm hkj, ↓reduceIte, one_mul]
  have e1 := hinv (SpecialLinearGroup.diag2n hik c hc0) (Pi.single i ((c - 1)⁻¹ * a))
    (Pi.single j b)
  rw [m1, m2, h1] at e1
  exact mul_left_cancel (e1.trans (mul_one _).symm)

include h1 h2 hinv in
theorem biadd_single_self {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) (i : Fin 3) (a b : F) :
    B (Pi.single i a) (Pi.single i b) = 1 := by
  obtain ⟨k, hki, -⟩ := exists_third (show i ≠ i + 1 by fin_cases i <;> decide)
  have hik : i ≠ k := fun h => hki h.symm
  have e1 := hinv (SpecialLinearGroup.transvection hik (1 : F)) (Pi.single k a) (Pi.single k b)
  rw [transvection_mulVec_single_self, transvection_mulVec_single_self, h1, h2, h2,
    biadd_single_ne B h1 hinv hc0 hc1 hki, biadd_single_ne B h1 hinv hc0 hc1 hik,
    mul_one, one_mul] at e1
  exact mul_left_cancel (e1.trans (mul_one _).symm)

include h1 h2 hinv in
theorem eq_one_of_biadd_inv {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) (x y : Fin 3 → F) :
    B x y = 1 := by
  have hs : ∀ i j a b, B (Pi.single i a) (Pi.single j b) = 1 := fun i j a b => by
    by_cases hij : i = j
    · subst hij
      exact biadd_single_self B h1 h2 hinv hc0 hc1 i a b
    · exact biadd_single_ne B h1 hinv hc0 hc1 hij a b
  have hrow : ∀ i a, B (Pi.single i a) y = 1 := fun i a => by
    rw [eq_sum_single y, h2, h2, hs, hs, hs, mul_one, mul_one]
  rw [eq_sum_single x, h1, h1, hrow, hrow, hrow, mul_one, mul_one]

end Biadd

section Add

variable {M : Type} [Group M] (s : (Fin 3 → F) → M) (h1 : ∀ x x', s (x + x') = s x * s x')
  (hinv : ∀ (g : SL(3, F)) x, s ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ x) = s x)

include h1 hinv in
theorem eq_one_of_add_inv (x : Fin 3 → F) : s x = 1 := by
  have hs : ∀ i a, s (Pi.single i a) = 1 := fun i a => by
    obtain ⟨k, hki, -⟩ := exists_third (show i ≠ i + 1 by fin_cases i <;> decide)
    have hik : i ≠ k := fun h => hki h.symm
    have e1 := hinv (SpecialLinearGroup.transvection hik (1 : F)) (Pi.single k a)
    rw [transvection_mulVec_single_self, h1] at e1
    exact mul_left_cancel (e1.trans (mul_one _).symm)
  rw [eq_sum_single x, h1, h1, hs, hs, hs, mul_one, mul_one]

end Add

end CFSG.Quasithin.SL3Small
