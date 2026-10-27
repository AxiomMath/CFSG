module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaFrameAux3

public section

namespace CFSG.StandardType.E6QTwo

open Module CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.StandardType.NoOffRest
open scoped Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V} {B : LinearMap.BilinForm (ZMod 3) V}

@[expose] def bY1 : Fin Tag.E6.rank → ZMod 3 := fun j => ([0, 0, 1, 2, 0, 2] : List (ZMod 3)).getD j.val 0

theorem bY1_spec : kDotP 3 bY1 = 0 ∧ f6 bY1 bY1 = 2 ∧ f6 bX0 bY1 = 0 := by
  decide +kernel

theorem exists_frame_of_norm_one (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {x : V} (hx : B x x = 1) :
    ∃ f : Fin 5 → V, (∀ i j, B (f i) (f j) = if i = j then 1 else 0) ∧ f 0 = x := by
  obtain ⟨X0, hX0⟩ := exists_cv_eq hP hV (c := bX0) bX0_spec.1
  obtain ⟨Y1, hY1⟩ := exists_cv_eq hP hV (c := bY1) bY1_spec.1
  have hX0n : B X0 X0 = 1 := by
    have h1 := cv_form hP hV hB X0 X0
    rw [hX0, bX0_spec.2] at h1
    exact (by decide : ∀ t : ZMod 3, 2 = 2 * t → t = 1) _ h1
  have hY1n : B Y1 Y1 = 1 := by
    have h1 := cv_form hP hV hB Y1 Y1
    rw [hY1, bY1_spec.2.1] at h1
    exact (by decide : ∀ t : ZMod 3, 2 = 2 * t → t = 1) _ h1
  have hXY : B X0 Y1 = 0 := by
    have h1 := cv_form hP hV hB X0 Y1
    rw [hX0, hY1, bY1_spec.2.2] at h1
    exact (by decide : ∀ t : ZMod 3, 0 = 2 * t → t = 0) _ h1
  have hne : ∀ z : V, B z z = 1 → z ≠ 0 := by
    rintro z hz rfl
    rw [map_zero] at hz
    exact absurd hz (by decide)
  obtain ⟨g, hg, hgx⟩ := exists_mem_e6Weyl_apply_eq hP hV hB hα (hne X0 hX0n) (hne x hx)
    (hX0n.trans hx.symm)
  obtain ⟨f, hf, hf0, -⟩ := exists_frame_of_perp hP hV hB hα hx (y := g Y1)
    (by rw [bilinForm_apply_e6Weyl hP hV hB hα hg]; exact hY1n)
    (by rw [← hgx, bilinForm_apply_e6Weyl hP hV hB hα hg]; exact hXY)
  exact ⟨f, hf, hf0⟩

end CFSG.StandardType.E6QTwo

end
