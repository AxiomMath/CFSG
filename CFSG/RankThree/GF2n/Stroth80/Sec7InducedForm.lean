module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem sec7_induced_form {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (f : LinearMap.BilinForm K E) (hf : f.Nondegenerate)
    (hr : f.IsRefl) (U : Submodule K E) (ψ : E →ₗ[K] E)
    (hr1 : LinearMap.range ψ = U) (hk1 : LinearMap.ker ψ = f.orthogonal U) :
    ∃ β : LinearMap.BilinForm K U, β.Nondegenerate ∧
      ∀ (x y : U) (c : E), ψ c = (y : E) → β x y = f x c := by
  obtain ⟨φ, hφ⟩ : ∃ φ : E →ₗ[K] U, ∀ c, (φ c : E) = ψ c :=
    ⟨ψ.codRestrict U (fun c => by rw [← hr1]; exact LinearMap.mem_range_self ψ c),
      fun c => rfl⟩
  have hφs : Function.Surjective φ := by
    intro y
    have hy : (y : E) ∈ LinearMap.range ψ := by
      rw [hr1]
      exact y.2
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hy
    exact ⟨c, Subtype.ext ((hφ c).trans hc)⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property φ LinearMap.id hφs
  have hsy : ∀ y : U, φ (s y) = y := fun y => LinearMap.congr_fun hs y
  have key : ∀ (x y : U) (c : E), ψ c = (y : E) → f (x : E) (s y) = f (x : E) c := by
    intro x y c hc
    have hψsy : ψ (s y) = (y : E) := by
      rw [← hφ (s y), hsy]
    have hψ0 : ψ (s y - c) = 0 := by
      rw [map_sub, hψsy, hc, sub_self]
    have hmem : s y - c ∈ LinearMap.ker ψ := LinearMap.mem_ker.mpr hψ0
    rw [hk1] at hmem
    have h1 := LinearMap.BilinForm.mem_orthogonal_iff.mp hmem (x : E) x.2
    rw [map_sub] at h1
    exact sub_eq_zero.mp h1
  have spec : ∀ (x y : U) (c : E), ψ c = (y : E) →
      (f.compl₁₂ U.subtype s) x y = f (x : E) c :=
    fun x y c hc => key x y c hc
  have hL : LinearMap.SeparatingLeft (f.compl₁₂ U.subtype s) := by
    intro x hx
    have hfx : ∀ c : E, f (x : E) c = 0 := by
      intro c
      rw [← spec x (φ c) c (hφ c).symm]
      exact hx (φ c)
    exact Subtype.ext (hf.1 (x : E) hfx)
  have hR : LinearMap.SeparatingRight (f.compl₁₂ U.subtype s) := by
    intro y hy
    obtain ⟨c, hc⟩ := hφs y
    have hψc : ψ c = (y : E) := by
      rw [← hφ c, hc]
    have hcorth : c ∈ f.orthogonal U := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      have h1 := spec ⟨n, hn⟩ y c hψc
      have h2 := hy ⟨n, hn⟩
      exact h1.symm.trans h2
    have hcker : c ∈ LinearMap.ker ψ := by
      rw [hk1]
      exact hcorth
    have hψ0 : ψ c = 0 := LinearMap.mem_ker.mp hcker
    exact Subtype.ext (hψc.symm.trans hψ0)
  exact ⟨f.compl₁₂ U.subtype s, And.intro hL hR, spec⟩

end CFSG.RankThree.GF2n.Stroth80
