module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaFrameAux3

public section

namespace CFSG.StandardType.E6QTwo

open Module CFSG.Assembly

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V} {B : LinearMap.BilinForm (ZMod 3) V}

theorem perp_facts (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {y : V} (hy : B y y = 2) :
    (∀ u : V, (∀ w : V, B w w = 2 → B w y = 0 → B w u = 0) → ∃ a : ZMod 3, u = a • y) ∧
      ∀ u : V, B u y = 0 → u ∈ Submodule.span (ZMod 3) {w : V | B w w = 2 ∧ B w y = 0} := by
  obtain ⟨f, hf, hfy⟩ := exists_frame_add_eq_of_root (B := B) hP hV hB hα hy
  have e01 : B (f 0 - f 1) (f 0 - f 1) = 2 := by
    simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right, hf]
    decide
  have e01y : B (f 0 - f 1) y = 0 := by
    rw [← hfy]
    simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.add_right, hf]
    decide
  have e23p : B (f 2 + f 3) (f 2 + f 3) = 2 := by
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hf]
    decide
  have e23py : B (f 2 + f 3) y = 0 := by
    rw [← hfy]
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hf]
    decide
  have e23m : B (f 2 - f 3) (f 2 - f 3) = 2 := by
    simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right, hf]
    decide
  have e23my : B (f 2 - f 3) y = 0 := by
    rw [← hfy]
    simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.add_right, hf]
    decide
  have e24p : B (f 2 + f 4) (f 2 + f 4) = 2 := by
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hf]
    decide
  have e24py : B (f 2 + f 4) y = 0 := by
    rw [← hfy]
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hf]
    decide
  have e24m : B (f 2 - f 4) (f 2 - f 4) = 2 := by
    simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right, hf]
    decide
  have e24my : B (f 2 - f 4) y = 0 := by
    rw [← hfy]
    simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.add_right, hf]
    decide
  have e34p : B (f 3 + f 4) (f 3 + f 4) = 2 := by
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hf]
    decide
  have e34m : B (f 3 - f 4) (f 3 - f 4) = 2 := by
    simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right, hf]
    decide
  constructor
  · intro u hu
    have h01 : B (f 0) u = B (f 1) u := by
      have h := hu (f 0 - f 1) e01 e01y
      rw [LinearMap.BilinForm.sub_left] at h
      exact sub_eq_zero.mp h
    have hp := hu (f 2 + f 3) e23p e23py
    have hm := hu (f 2 - f 3) e23m e23my
    rw [LinearMap.BilinForm.add_left] at hp
    rw [LinearMap.BilinForm.sub_left] at hm
    have h2 : B (f 2) u = 0 :=
      (by decide : ∀ a b : ZMod 3, a + b = 0 → a - b = 0 → a = 0) _ _ hp hm
    have h3 : B (f 3) u = 0 :=
      (by decide : ∀ a b : ZMod 3, a + b = 0 → a - b = 0 → b = 0) _ _ hp hm
    have h4 : B (f 4) u = 0 := by
      have h := hu (f 2 + f 4) e24p e24py
      rw [LinearMap.BilinForm.add_left, h2] at h
      exact (by decide : ∀ b : ZMod 3, 0 + b = 0 → b = 0) _ h
    refine ⟨B u (f 0), ?_⟩
    have hsym : ∀ i : Fin 5, B u (f i) = B (f i) u := fun i =>
      bilinForm_symm hP hV hB u (f i)
    conv_lhs => rw [eq_sum_frame (B := B) hV hf u]
    rw [Fin.sum_univ_five]
    simp only [hsym, zero_smul, add_zero]
    rw [← h01, h2, h3, h4]
    simp only [zero_smul]
    rw [← smul_add, hfy]
    simp
  · intro u huy
    set M : Submodule (ZMod 3) V :=
      Submodule.span (ZMod 3) {w : V | B w w = 2 ∧ B w y = 0}
    have hM : ∀ w : V, B w w = 2 → B w y = 0 → w ∈ M :=
      fun w hw hwy => Submodule.subset_span ⟨hw, hwy⟩
    have h01 : f 0 - f 1 ∈ M := hM _ e01 e01y
    have h23p : f 2 + f 3 ∈ M := hM _ e23p e23py
    have h23m : f 2 - f 3 ∈ M := hM _ e23m e23my
    have h24p : f 2 + f 4 ∈ M := hM _ e24p e24py
    have h24m : f 2 - f 4 ∈ M := hM _ e24m e24my
    have h34p : f 3 + f 4 ∈ M := hM _ e34p (by
      rw [← hfy]
      simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right, hf]
      decide)
    have h34m : f 3 - f 4 ∈ M := hM _ e34m (by
      rw [← hfy]
      simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.add_right, hf]
      decide)
    have h2 : f 2 ∈ M := by
      have hs : (f 2 + f 3) + (f 2 - f 3) = (2 : ZMod 3) • f 2 := by
        rw [two_smul]
        abel
      have hm := Submodule.smul_mem M (2 : ZMod 3) (Submodule.add_mem M h23p h23m)
      rwa [hs, smul_smul, show (2 * 2 : ZMod 3) = 1 by decide, one_smul] at hm
    have h3 : f 3 ∈ M := by
      have hs : (f 3 + f 4) + (f 3 - f 4) = (2 : ZMod 3) • f 3 := by
        rw [two_smul]
        abel
      have hm := Submodule.smul_mem M (2 : ZMod 3) (Submodule.add_mem M h34p h34m)
      rwa [hs, smul_smul, show (2 * 2 : ZMod 3) = 1 by decide, one_smul] at hm
    have h4 : f 4 ∈ M := by
      have hs : (f 4 + f 2) + (f 4 - f 2) = (2 : ZMod 3) • f 4 := by
        rw [two_smul]
        abel
      have h42p : f 4 + f 2 ∈ M := by
        rw [add_comm]
        exact h24p
      have h42m : f 4 - f 2 ∈ M := by
        have hneg : -(f 2 - f 4) ∈ M := Submodule.neg_mem M h24m
        simpa only [neg_sub] using hneg
      have hm := Submodule.smul_mem M (2 : ZMod 3) (Submodule.add_mem M h42p h42m)
      rwa [hs, smul_smul, show (2 * 2 : ZMod 3) = 1 by decide, one_smul] at hm
    have huy' : B u (f 0) + B u (f 1) = 0 := by
      have h := huy
      rw [← hfy, LinearMap.BilinForm.add_right] at h
      exact h
    have hc1 : B u (f 1) = -B u (f 0) :=
      (by decide : ∀ a b : ZMod 3, a + b = 0 → b = -a) _ _ huy'
    have hexp : u = B u (f 0) • f 0 + B u (f 1) • f 1 + B u (f 2) • f 2 +
        B u (f 3) • f 3 + B u (f 4) • f 4 := by
      conv_lhs => rw [eq_sum_frame (B := B) hV hf u]
      rw [Fin.sum_univ_five]
    have hu_eq : u = B u (f 0) • (f 0 - f 1) + B u (f 2) • f 2 +
        B u (f 3) • f 3 + B u (f 4) • f 4 := by
      conv_lhs => rw [hexp]
      rw [hc1]
      rw [smul_sub]
      rw [show (-(B u (f 0))) • f 1 = -(B u (f 0) • f 1) from neg_smul _ _]
      abel
    rw [hu_eq]
    exact Submodule.add_mem M
      (Submodule.add_mem M
        (Submodule.add_mem M (Submodule.smul_mem M _ h01) (Submodule.smul_mem M _ h2))
        (Submodule.smul_mem M _ h3)) (Submodule.smul_mem M _ h4)

end CFSG.StandardType.E6QTwo

end
