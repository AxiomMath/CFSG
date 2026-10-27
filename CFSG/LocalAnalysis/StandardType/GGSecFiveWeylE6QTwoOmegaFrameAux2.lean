module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaFrame

public section

namespace CFSG.StandardType.E6QTwo

open Module CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.StandardType.NoOffRest
open scoped Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V} {B : LinearMap.BilinForm (ZMod 3) V}

@[expose] def bE : Fin 5 → (Fin Tag.E6.rank → ZMod 3)
  | 0 => ![0, 0, 1, 1, 1, 0]
  | 1 => ![0, 0, 1, 2, 0, 2]
  | 2 => ![0, 0, 1, 2, 2, 1]
  | 3 => ![1, 1, 1, 1, 0, 0]
  | 4 => ![1, 2, 1, 2, 0, 0]

theorem bE_hyp (i : Fin 5) : kDotP 3 (bE i) = 0 := by
  fin_cases i <;> decide +kernel

theorem bE_gram (i j : Fin 5) : f6 (bE i) (bE j) = if i = j then 2 else 0 := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem exists_baseFrame (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) :
    ∃ E : Fin 5 → V, (∀ i j, B (E i) (E j) = if i = j then 1 else 0) ∧
      B (E 0 + E 1) (E 0 + E 1) = 2 := by
  choose E hE using fun i => exists_cv_eq (α := α) hP hV (bE_hyp i)
  have hBij : ∀ i j, B (E i) (E j) = if i = j then 1 else 0 := by
    intro i j
    have h := cv_form (α := α) hP hV hB (E i) (E j)
    rw [hE i, hE j, bE_gram] at h
    by_cases hij : i = j
    · rw [if_pos hij] at h ⊢
      exact (by decide : ∀ t : ZMod 3, 2 = 2 * t → t = 1) _ h
    · rw [if_neg hij] at h ⊢
      exact (by decide : ∀ t : ZMod 3, 0 = 2 * t → t = 0) _ h
  refine ⟨E, hBij, ?_⟩
  simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hBij]
  decide

theorem exists_frame_add_eq_of_root
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {y : V} (hy : B y y = 2) :
    ∃ f : Fin 5 → V, (∀ i j, B (f i) (f j) = if i = j then 1 else 0) ∧ f 0 + f 1 = y := by
  obtain ⟨E, hE, hEr⟩ := exists_baseFrame (B := B) hP hV hB
  obtain ⟨g, hg, hgy⟩ :=
    exists_mem_e6Weyl_apply_eq_of_norm_two (B := B) hP hV hB hα hEr hy
  refine ⟨fun i => g (E i), ?_, ?_⟩
  · intro i j
    rw [bilinForm_apply_e6Weyl (B := B) hP hV hB hα hg]
    exact hE i j
  · show g (E 0) + g (E 1) = y
    rw [← map_add g (E 0) (E 1), hgy]

end CFSG.StandardType.E6QTwo

end
