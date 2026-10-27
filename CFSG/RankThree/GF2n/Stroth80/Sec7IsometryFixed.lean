module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem sec7_fixed_perp_range {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (f : LinearMap.BilinForm K E) (g : E ≃ₗ[K] E) (hg : ∀ e e', f (g e) (g e') = f e e') :
    ∀ c : E, g c = c → ∀ e : E, f c (g e - e) = 0 := by
  intro c hc e
  have h1 : f (g c) (g e) = f c e := hg c e
  rw [hc] at h1
  rw [map_sub, h1, sub_self]

theorem sec7_ker_sub_one_eq_perp_range {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (f : LinearMap.BilinForm K E) (hf : f.Nondegenerate)
    (hr : f.IsRefl) (g : E ≃ₗ[K] E) (hg : ∀ e e', f (g e) (g e') = f e e') :
    LinearMap.ker ((g : E →ₗ[K] E) - 1) =
      f.orthogonal (LinearMap.range ((g : E →ₗ[K] E) - 1)) := by
  have horth : ∀ W : Submodule K E,
      Module.finrank K W + Module.finrank K (f.orthogonal W) = Module.finrank K E := by
    intro W
    have h := LinearMap.BilinForm.finrank_add_finrank_orthogonal hr W
    rw [LinearMap.BilinForm.orthogonal_top_eq_bot hf, inf_bot_eq, finrank_bot, add_zero] at h
    exact h
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · intro c hc
    rw [LinearMap.mem_ker] at hc
    have hgc : g c = c := sub_eq_zero.mp (by simpa using hc)
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    obtain ⟨e, rfl⟩ := LinearMap.mem_range.mp hn
    have h := sec7_fixed_perp_range f g hg c hgc e
    simpa using hr.eq_zero h
  · have h1 := LinearMap.finrank_range_add_finrank_ker ((g : E →ₗ[K] E) - 1)
    have h2 := horth (LinearMap.range ((g : E →ₗ[K] E) - 1))
    omega

end CFSG.RankThree.GF2n.Stroth80
