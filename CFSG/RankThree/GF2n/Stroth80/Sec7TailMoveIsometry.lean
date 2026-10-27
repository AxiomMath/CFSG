module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveOpm
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup
open scoped commutatorElement

variable {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

theorem ker_opm_eq_orthogonal_range (B : LinearMap.BilinForm K E) (hnd : B.Nondegenerate)
    (hrefl : B.IsRefl) (g : E ≃ₗ[K] E) (hg : ∀ x y, B (g x) (g y) = B x y) :
    LinearMap.ker (opm g) = B.orthogonal (LinearMap.range (opm g)) := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker, opm_apply, sub_eq_zero] at hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    rintro n ⟨y, rfl⟩
    have h1 := hg y x
    rw [hx] at h1
    simp only [opm_apply, map_sub, LinearMap.sub_apply, h1, sub_self]
  · intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx
    have key : ∀ w, B w (g x - x) = 0 := by
      intro w
      obtain ⟨z, rfl⟩ : ∃ z, g z = w := ⟨g.symm w, g.apply_symm_apply w⟩
      have h1 : B (g z) x = B z x := by
        have h := hx (opm g z) (LinearMap.mem_range_self (opm g) z)
        rw [opm_apply, map_sub, LinearMap.sub_apply] at h
        exact sub_eq_zero.mp h
      simp only [map_sub, LinearMap.sub_apply, hg z x, h1, sub_self]
    have hz : g x - x = 0 := hnd.1 (g x - x) (fun w => hrefl w (g x - x) (key w))
    rw [LinearMap.mem_ker, opm_apply]
    exact hz

theorem iSup_range_opm_isotropic (B : LinearMap.BilinForm K E) (hnd : B.Nondegenerate)
    (hrefl : B.IsRefl) {ι : Type*} (g : ι → (E ≃ₗ[K] E)) (hg : ∀ i x y, B (g i x) (g i y) = B x y)
    (hquad : ∀ i j x, opm (g i) (opm (g j) x) = 0) :
    ∀ x ∈ (⨆ i, LinearMap.range (opm (g i))), ∀ y ∈ (⨆ i, LinearMap.range (opm (g i))),
      B x y = 0 := by
  have hpair : ∀ i j, ∀ a ∈ LinearMap.range (opm (g i)), ∀ b ∈ LinearMap.range (opm (g j)),
      B a b = 0 := by
    intro i j a ha b hb
    obtain ⟨x, rfl⟩ := hb
    have hker : opm (g j) x ∈ LinearMap.ker (opm (g i)) := LinearMap.mem_ker.mpr (hquad i j x)
    rw [ker_opm_eq_orthogonal_range B hnd hrefl (g i) (hg i)] at hker
    exact LinearMap.BilinForm.mem_orthogonal_iff.mp hker a ha
  have step1 : ∀ i, ∀ a ∈ LinearMap.range (opm (g i)),
      ∀ y ∈ (⨆ j, LinearMap.range (opm (g j))), B a y = 0 := by
    intro i a ha y hy
    refine Submodule.iSup_induction (motive := fun z => B a z = 0) _ hy ?_ ?_ ?_
    · intro j b hb
      exact hpair i j a ha b hb
    · simp
    · intro b c hb hc
      simp [map_add, hb, hc]
  intro x hx y hy
  refine Submodule.iSup_induction (motive := fun z => B z y = 0) _ hx ?_ ?_ ?_
  · intro i a ha
    exact step1 i a ha y hy
  · simp
  · intro a b ha hb
    simp [map_add, LinearMap.add_apply, ha, hb]

theorem sub_mem_orthogonal_of_fixes (B : LinearMap.BilinForm K E) (u : E ≃ₗ[K] E)
    (hu : ∀ x y, B (u x) (u y) = B x y) (T : Submodule K E) (hT : ∀ w ∈ T, u w = w) (q : E) :
    u q - q ∈ B.orthogonal T := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro w hw
  have h1 := hu w q
  rw [hT w hw] at h1
  simp only [map_sub, LinearMap.sub_apply, h1, sub_self]

theorem mul_comm_of_fixes (B : LinearMap.BilinForm K E) (u v : E ≃ₗ[K] E)
    (hu : ∀ x y, B (u x) (u y) = B x y) (T : Submodule K E) (hT : ∀ w ∈ T, u w = w)
    (hr : LinearMap.range (opm v) ≤ T) (hk : B.orthogonal T ≤ LinearMap.ker (opm v)) :
    u * v = v * u := by
  ext q
  simp only [LinearEquiv.mul_apply]
  have hvq : opm v q ∈ T := hr (LinearMap.mem_range_self (opm v) q)
  have h1 : u (v q) - u q = v q - q := by
    have h := hT (opm v q) hvq
    rw [opm_apply, map_sub] at h
    exact h
  have h2 : v (u q - q) = u q - q := by
    have h := LinearMap.mem_ker.mp (hk (sub_mem_orthogonal_of_fixes B u hu T hT q))
    rw [opm_apply] at h
    exact sub_eq_zero.mp h
  have h3 : v (u q) = v (u q - q) + v q := by
    rw [← map_add, sub_add_cancel]
  rw [sub_eq_iff_eq_add] at h1
  rw [h3, h2, h1]
  abel

end CFSG.RankThree.GF2n.Stroth80
