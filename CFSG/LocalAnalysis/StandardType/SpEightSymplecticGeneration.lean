module

public import CFSG.LocalAnalysis.StandardType.SpEightTransvections
public import CFSG.Fischer.Classification.Symplectic.OrthoGenSymplectic

public section

namespace CFSG.StandardType.SpEight

open Matrix CFSG.Open CFSG.Blueprint.EvenSource

theorem statedSp_eq_closure_tvGL :
    StatedSp 4 (ZMod 2) = Subgroup.closure {g | ∃ w : Vec, w ≠ 0 ∧ g = tvGL w} := by
  let b : LinearMap.BilinForm (ZMod 2) Vec := Matrix.toBilin' Jm
  have hb_eq : ∀ x y : Vec, b x y = omega x y := fun x y => Matrix.toBilin'_apply' Jm x y
  have halt : ∀ x : Vec, b x x = 0 := fun x => by rw [hb_eq x x]; exact omega_self x
  have hnd : ∀ x : Vec, (∀ y : Vec, b x y = 0) → x = 0 := fun x hx =>
    eq_zero_of_omega_eq_zero fun u => by rw [← hb_eq x u]; exact hx u
  have hgrp : (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y) =
      StatedSp 4 (ZMod 2) := by
    apply le_antisymm
    · intro A hA
      rw [mem_statedSp_iff_omega]
      intro u v
      rw [← hb_eq, ← hb_eq]
      exact (CFSG.Fischer.Classification.mem_fischerMatrixGroup_bilin_iff b A).mp hA u v
    · intro A hA
      rw [CFSG.Fischer.Classification.mem_fischerMatrixGroup_bilin_iff]
      intro x y
      rw [hb_eq, hb_eq]
      exact (mem_statedSp_iff_omega A).mp hA x y
  have hset : fischerTransvections (fun x y => b x y) (fun v => v ≠ 0) =
      {g | ∃ w : Vec, w ≠ 0 ∧ g = tvGL w} := by
    ext g
    constructor
    · rintro ⟨v, hv, hgv⟩
      refine ⟨v, hv, ?_⟩
      exact Units.ext ((Matrix.ext_iff_mulVec).mpr fun x => by
        rw [hgv x, tvGL_mulVec]
        simp only [hb_eq])
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, fun x => by rw [tvGL_mulVec]; simp only [hb_eq]⟩
  rw [← hgrp, CFSG.Fischer.Classification.fischerMatrixGroup_bilin_eq_closure b halt hnd, hset]

end CFSG.StandardType.SpEight
