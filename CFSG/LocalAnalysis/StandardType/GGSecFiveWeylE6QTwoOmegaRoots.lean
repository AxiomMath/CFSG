module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaRootRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaRootsD4
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaRootsOrbit
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaFrameAux4
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaFrameAux5
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaFrameAux6

public section

namespace CFSG.StandardType.E6QTwo

open Module CFSG.Assembly

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V} {B : LinearMap.BilinForm (ZMod 3) V}

theorem phiD_facts (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {x y : V} (hx : B x x = 1) (hyx : ∀ a : ZMod 3, y ≠ a • x)
    (h12 : 12 ≤ Set.ncard {v : V | B v v = 2 ∧ B v x = 0 ∧ B v y = 0}) :
    Set.ncard {v : V | B v v = 2 ∧ B v x = 0 ∧ B v y = 0} = 12 ∧
      (∀ u : V, (∀ v : V, B v v = 2 → B v x = 0 → B v y = 0 → B v u = 0) →
        ∃ a b : ZMod 3, u = a • x + b • y) ∧
      (∀ v : V, B v v = 2 → B v x = 0 → B v y = 0 →
        ∃ w : V, B w w = 2 ∧ B w x = 0 ∧ B w y = 0 ∧ w ≠ v ∧ w ≠ -v ∧ B v w ≠ 0) ∧
      ∀ a b : ZMod 3, b ≠ 0 →
        (B x (a • x + b • y) ≠ 0 ∧ B (a • x + b • y) (a • x + b • y) = 2) ∨
          (B x (a • x + b • y) = 0 ∧ B (a • x + b • y) (a • x + b • y) = 1) := by
  obtain ⟨f, hf, hf0⟩ := exists_frame_of_norm_one hP hV hB hα hx
  exact phiD_facts_of_frame hV hf hf0 hyx h12

theorem exists_mem_closure_rootRefl_apply_eq
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {y v w : V} (hy : B y y = 2) (hv : B v v = 2) (hw : B w w = 2) (hvy : B v y = 0)
    (hwy : B w y = 0) :
    ∃ g ∈ Subgroup.closure {r : V ≃ₗ[ZMod 3] V | ∃ u : V, ∃ hu : B u u = 2, B u y = 0 ∧
      r = rootRefl (B := B) u hu}, g v = w := by
  change ∃ g ∈ Subgroup.closure (rootReflOrth (B := B) y), g v = w
  obtain ⟨f, hf, hf01⟩ := exists_frame_add_eq_of_root hP hV hB hα hy
  have hFy : frameCoord hV hf y = stdY0 := by
    rw [← hf01, map_add, frameCoord_frame hV hf 0, frameCoord_frame hV hf 1]
    exact stdY0_eq.symm
  obtain ⟨a, haW, hav⟩ := exists_stdFrameWord_T30 hV hf hFy (v := v) hv hvy
  obtain ⟨b, hbW, hbw⟩ := exists_stdFrameWord_T30 hV hf hFy (v := w) hw hwy
  refine ⟨b * a⁻¹, Subgroup.mul_mem _ hbW (Subgroup.inv_mem _ haW), ?_⟩
  have hinv : a⁻¹ v = (frameCoord hV hf).symm stdB30 := by
    rw [LinearEquiv.coe_inv]
    apply a.injective
    rw [LinearEquiv.apply_symm_apply, hav]
  rw [LinearEquiv.mul_apply, hinv, hbw]

theorem e6Weyl_le_closure_insert (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {y w : V} (hy : B y y = 2) (hw : B w w = 2) (hwy : B w y ≠ 0) (hwy₁ : w ≠ y)
    (hwy₂ : w ≠ -y) :
    e6Weyl hα ≤ Subgroup.closure (insert (rootRefl (B := B) w hw)
      {r : V ≃ₗ[ZMod 3] V | ∃ u : V, ∃ hu : B u u = 2, B u y = 0 ∧
        r = rootRefl (B := B) u hu}) := by
  change e6Weyl hα ≤ Subgroup.closure (insert (rootRefl (B := B) w hw)
    (rootReflOrth (B := B) y))
  rcases (by decide : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2) (B w y) with h0 | h1 | h2
  · exact absurd h0 hwy
  · exact e6Weyl_le_closure_insert_of_one hP hV hB hα hy hw h1 hwy₂
  · have hw' : B (-w) (-w) = 2 := by
      rw [LinearMap.BilinForm.neg_left, LinearMap.BilinForm.neg_right, neg_neg]
      exact hw
    have h1' : B (-w) y = 1 := by
      rw [LinearMap.BilinForm.neg_left, h2]
      decide
    have hne2 : -w ≠ -y := by
      intro h
      exact hwy₁ (neg_inj.mp h)
    have hle := e6Weyl_le_closure_insert_of_one hP hV hB hα hy hw' h1' hne2
    have heq : rootRefl (B := B) (-w) hw' = rootRefl (B := B) w hw :=
      rootRefl_neg (B := B) w hw
    rw [heq] at hle
    exact hle

end CFSG.StandardType.E6QTwo

end
