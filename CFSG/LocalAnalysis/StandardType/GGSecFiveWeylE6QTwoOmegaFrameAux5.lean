module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaFrameAux4

public section

namespace CFSG.StandardType.E6QTwo

open Module CFSG.Assembly
open scoped Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V} {B : LinearMap.BilinForm (ZMod 3) V}

abbrev stdSet (d : Fin 5 → ZMod 3) : Prop :=
  ∃ k : Fin 5, ∃ ε : ZMod 3, ε ≠ 0 ∧ d = ε • Pi.single k 1

theorem stdRefl_stdSet_single :
    ∀ (c : Fin 5 → ZMod 3), c ⬝ᵥ c = 2 → (c 0 = 0 ∨ c 1 = 0) →
      ∀ (k : Fin 5) (ε : ZMod 3), ε ≠ 0 → stdSet (stdRefl c (ε • Pi.single k 1)) := by
  decide +kernel

theorem stdRefl_stdSet {c : Fin 5 → ZMod 3} (hc : c ⬝ᵥ c = 2) (h0 : c 0 = 0 ∨ c 1 = 0) :
    ∀ d, stdSet d → stdSet (stdRefl c d) := by
  rintro d ⟨k, ε, hε, rfl⟩
  exact stdRefl_stdSet_single c hc h0 k ε hε

theorem stdRefl_stdSet_iff {c : Fin 5 → ZMod 3} (hc : c ⬝ᵥ c = 2) (h0 : c 0 = 0 ∨ c 1 = 0)
    (d : Fin 5 → ZMod 3) : stdSet d ↔ stdSet (stdRefl c d) := by
  refine ⟨stdRefl_stdSet hc h0 d, fun h => ?_⟩
  have h' := stdRefl_stdSet hc h0 (stdRefl c d) h
  rwa [stdRefl_involutive hc d] at h'

theorem exists_rootRefl_not_mem_closure
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {x y : V} (hx : B x x = 1) (hy : B y y = 1) (hxy : B x y = 0) :
    ∃ w : V, ∃ hw : B w w = 2, rootRefl (B := B) w hw ∉ Subgroup.closure
      {r : V ≃ₗ[ZMod 3] V | ∃ u : V, ∃ hu : B u u = 2, (B u x = 0 ∨ B u y = 0) ∧
        r = rootRefl (B := B) u hu} := by
  obtain ⟨f, hf, hf0, hf1⟩ := exists_frame_of_perp (B := B) hP hV hB hα hx hy hxy
  let S : Set V := {v : V | ∃ i : Fin 5, v = f i ∨ v = (2 : ZMod 3) • f i}
  have hinj := (frameCoord hV hf).injective
  have hcoord_norm : ∀ u : V,
      frameCoord hV hf u ⬝ᵥ frameCoord hV hf u = B u u := fun u =>
    (frameCoord_form hV hf u u).symm
  have hcoord0 : ∀ u : V, frameCoord hV hf u 0 = B u x := by
    intro u
    rw [frameCoord_apply, hf0]
  have hcoord1 : ∀ u : V, frameCoord hV hf u 1 = B u y := by
    intro u
    rw [frameCoord_apply, hf1]
  have hmemS : ∀ v : V, v ∈ S ↔ stdSet (frameCoord hV hf v) := by
    intro v
    constructor
    · rintro ⟨i, h | h⟩
      · refine ⟨i, 1, by decide, ?_⟩
        rw [h, frameCoord_frame hV hf i, one_smul]
      · refine ⟨i, 2, by decide, ?_⟩
        rw [h, map_smul, frameCoord_frame hV hf i]
    · rintro ⟨k, ε, hε, hκ⟩
      refine ⟨k, ?_⟩
      have hε12 : ε = 1 ∨ ε = 2 :=
        (by decide : ∀ t : ZMod 3, t ≠ 0 → t = 1 ∨ t = 2) ε hε
      have h : ε • f k = v := by
        apply hinj
        rw [map_smul, frameCoord_frame hV hf k]
        exact hκ.symm
      rcases hε12 with rfl | rfl
      · left
        rw [one_smul] at h
        exact h.symm
      · right
        exact h.symm
  have hgen : ∀ g ∈ Subgroup.closure {r : V ≃ₗ[ZMod 3] V | ∃ u : V, ∃ hu : B u u = 2,
        (B u x = 0 ∨ B u y = 0) ∧ r = rootRefl (B := B) u hu},
      ∀ v : V, v ∈ S ↔ g v ∈ S := by
    intro g hg
    refine Subgroup.closure_induction (p := fun g _ => ∀ v : V, v ∈ S ↔ g v ∈ S) ?_ ?_ ?_ ?_ hg
    · rintro r ⟨u, hu, huxy, rfl⟩
      intro v
      have hc2 : frameCoord hV hf u ⬝ᵥ frameCoord hV hf u = 2 := by
        rw [hcoord_norm u, hu]
      have hc0 : frameCoord hV hf u 0 = 0 ∨ frameCoord hV hf u 1 = 0 := by
        rcases huxy with h | h
        · left
          rw [hcoord0 u]
          exact h
        · right
          rw [hcoord1 u]
          exact h
      rw [hmemS v, hmemS (rootRefl (B := B) u hu v), frameCoord_rootRefl hV hf hu v]
      exact stdRefl_stdSet_iff hc2 hc0 _
    · intro v
      rfl
    · intro a b _ _ ha hb v
      rw [LinearEquiv.mul_apply]
      exact (hb v).trans (ha (b v))
    · intro a _ ha v
      have h := ha (a.symm v)
      rw [LinearEquiv.apply_symm_apply] at h
      exact h.symm
  let w : V := ∑ i, f i
  have hwfi : ∀ i : Fin 5, B w (f i) = 1 := by
    intro i
    have hwsum : w = ∑ j : Fin 5, (1 : ZMod 3) • f j := by
      simp only [w, one_smul]
    rw [hwsum, map_sum]
    simp only [LinearMap.sum_apply, LinearMap.BilinForm.smul_left, hf, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl, mul_one]
    · intro j _ hji
      rw [if_neg hji, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hw : B w w = 2 := by
    rw [apply_eq_sum_frame (B := B) hV hf w w]
    simp only [hwfi, mul_one]
    decide
  have hcw : frameCoord hV hf w = fun _ => (1 : ZMod 3) := by
    funext i
    exact hwfi i
  have hw0 : rootRefl (B := B) w hw (f 0) ∉ S := by
    intro hmem
    have hs := (hmemS (rootRefl (B := B) w hw (f 0))).mp hmem
    rw [frameCoord_rootRefl hV hf hw (f 0), frameCoord_frame hV hf 0, hcw] at hs
    exact (by decide : ¬ stdSet (stdRefl (fun _ : Fin 5 => (1 : ZMod 3)) (Pi.single 0 1))) hs
  refine ⟨w, hw, fun hcl => ?_⟩
  have hp := hgen (rootRefl (B := B) w hw) hcl (f 0)
  exact hw0 (hp.mp ⟨0, Or.inl rfl⟩)

end CFSG.StandardType.E6QTwo

end
