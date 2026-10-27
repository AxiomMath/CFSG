module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open Module

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  {B : LinearMap.BilinForm K E} {V W : Submodule K E} {D : E →ₗ[K] E}

theorem orthogonal_range_sup_eq (hnd : B.Nondegenerate) (hW : W = B.orthogonal V)
    (hadj : ∀ x, ∀ w ∈ W, B (D x) w = -B x (D w)) :
    B.orthogonal (LinearMap.range D ⊔ V) = W ⊓ LinearMap.ker D := by
  ext x
  rw [LinearMap.BilinForm.mem_orthogonal_iff, Submodule.mem_inf, LinearMap.mem_ker]
  constructor
  · intro h
    have hxW : x ∈ W := by
      rw [hW, LinearMap.BilinForm.mem_orthogonal_iff]
      exact fun v hv => h v (Submodule.mem_sup_right hv)
    refine ⟨hxW, hnd.2 _ fun e => ?_⟩
    have h1 := h (D e) (Submodule.mem_sup_left (LinearMap.mem_range_self D e))
    rwa [hadj e x hxW, neg_eq_zero] at h1
  · rintro ⟨hxW, hDx⟩ y hy
    obtain ⟨y₁, hy₁, v, hv, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨e, rfl⟩ := LinearMap.mem_range.mp hy₁
    have hvx : B v x = 0 := by
      rw [hW, LinearMap.BilinForm.mem_orthogonal_iff] at hxW
      exact hxW v hv
    rw [map_add, LinearMap.add_apply, hadj e x hxW, hDx, map_zero, neg_zero, hvx, add_zero]

theorem range_sup_eq_orthogonal (hnd : B.Nondegenerate) (hrefl : B.IsRefl)
    (hW : W = B.orthogonal V) (hadj : ∀ x, ∀ w ∈ W, B (D x) w = -B x (D w)) :
    LinearMap.range D ⊔ V = B.orthogonal (W ⊓ LinearMap.ker D) := by
  rw [← orthogonal_range_sup_eq hnd hW hadj,
    LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl]

end CFSG.RankThree.GF2n.Stroth80.S715L
