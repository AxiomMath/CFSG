module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem sec7_finrank_map_orthogonal {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (B : LinearMap.BilinForm K E) (hB : B.Nondegenerate)
    (hr : B.IsRefl) (ψ : E →ₗ[K] E)
    (hker : LinearMap.ker ψ = B.orthogonal (LinearMap.range ψ)) (U : Submodule K E) :
    Module.finrank K ((B.orthogonal U).map ψ) =
      Module.finrank K (LinearMap.range ψ) - Module.finrank K ↥(U ⊓ LinearMap.range ψ) := by
  have horth : ∀ W : Submodule K E,
      Module.finrank K W + Module.finrank K (B.orthogonal W) = Module.finrank K E := by
    intro W
    have h := LinearMap.BilinForm.finrank_add_finrank_orthogonal hr W
    rw [LinearMap.BilinForm.orthogonal_top_eq_bot hB, inf_bot_eq, finrank_bot, add_zero] at h
    exact h
  have hk : (LinearMap.ker (ψ.domRestrict (B.orthogonal U))).map (B.orthogonal U).subtype =
      B.orthogonal U ⊓ LinearMap.ker ψ := by
    ext x
    constructor
    · rintro ⟨⟨y, hy⟩, hy', rfl⟩
      exact Submodule.mem_inf.mpr ⟨hy, by simpa using hy'⟩
    · rintro ⟨hx, hx'⟩
      exact Submodule.mem_map.mpr ⟨⟨x, hx⟩, by simpa using hx', rfl⟩
  have hrange : LinearMap.range (ψ.domRestrict (B.orthogonal U)) = (B.orthogonal U).map ψ := by
    ext y
    constructor
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker (ψ.domRestrict (B.orthogonal U))
  have hfin := Submodule.finrank_map_subtype_eq (B.orthogonal U)
    (LinearMap.ker (ψ.domRestrict (B.orthogonal U)))
  rw [hk] at hfin
  rw [hrange, ← hfin] at hrn
  have hinf : B.orthogonal U ⊓ B.orthogonal (LinearMap.range ψ) =
      B.orthogonal (U ⊔ LinearMap.range ψ) := by
    ext x
    simp only [Submodule.mem_inf, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · rintro ⟨hU, hR⟩ n hn
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hn
      simp [hU y hy, hR z hz]
    · intro hx
      exact ⟨fun n hn => hx n (Submodule.mem_sup_left hn),
        fun n hn => hx n (Submodule.mem_sup_right hn)⟩
  have hW : B.orthogonal U ⊓ LinearMap.ker ψ = B.orthogonal (U ⊔ LinearMap.range ψ) := by
    rw [hker, hinf]
  rw [hW] at hrn
  have hU1 := horth U
  have hS1 := horth (U ⊔ LinearMap.range ψ)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U (LinearMap.range ψ)
  have hmono : Module.finrank K ↥(U ⊓ LinearMap.range ψ) ≤
      Module.finrank K (LinearMap.range ψ) :=
    Submodule.finrank_mono inf_le_right
  have hadd : Module.finrank K ((B.orthogonal U).map ψ) +
      Module.finrank K ↥(U ⊓ LinearMap.range ψ) = Module.finrank K (LinearMap.range ψ) := by
    omega
  omega

end CFSG.RankThree.GF2n.Stroth80
