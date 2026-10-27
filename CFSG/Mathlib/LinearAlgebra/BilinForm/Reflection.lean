module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.RingTheory.LocalRing.Basic

public section

namespace LinearMap.BilinMap

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem apply_left_eq_zero_of_preReflection (B : V →ₗ[K] V →ₗ[K] W) (hB : B.IsAlt)
    (h2 : (2 : K) ≠ 0) (e : V) (α : V →ₗ[K] K) (hα : α e = 2)
    (hρ : ∀ u v, B (u - α u • e) (v - α v • e) = B u v) : B e = 0 := by
  ext v
  have he : e - α e • e = -e := by
    rw [hα, two_smul K e]
    abel
  have h := hρ e v
  rw [he, map_neg, LinearMap.neg_apply, map_sub, map_smul, hB e, smul_zero,
    sub_zero] at h
  have hzero : (2 : K) • B e v = 0 := by
    rw [two_smul]
    exact neg_eq_iff_add_eq_zero.mp h
  exact (smul_eq_zero.mp hzero).resolve_left h2

theorem two_le_finrank_range_of_isAlt [FiniteDimensional K V]
    (B : V →ₗ[K] V →ₗ[K] W) (hB : B.IsAlt) (hne : B ≠ 0) :
    2 ≤ Module.finrank K B.range := by
  classical
  obtain ⟨u, v, huv⟩ : ∃ u v, B u v ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (by ext u v; exact h u v)
  have hvu : B v u ≠ 0 := by
    intro hzero
    have hcross := hB (u + v)
    simp only [map_add, LinearMap.add_apply, hB u, hB v, hzero, zero_add,
      add_zero] at hcross
    exact huv hcross
  let a : B.range := ⟨B u, ⟨u, rfl⟩⟩
  let b : B.range := ⟨B v, ⟨v, rfl⟩⟩
  have hab : LinearIndependent K ![a, b] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hv : s • B u v + t • B v v = 0 :=
      congrArg (fun f : B.range => (f : V →ₗ[K] W) v) hst
    rw [hB v, smul_zero, add_zero] at hv
    have hs : s = 0 := (smul_eq_zero.mp hv).resolve_right huv
    have hu : s • B u u + t • B v u = 0 :=
      congrArg (fun f : B.range => (f : V →ₗ[K] W) u) hst
    rw [hs, zero_smul, zero_add] at hu
    exact ⟨hs, (smul_eq_zero.mp hu).resolve_right hvu⟩
  simpa using hab.fintype_card_le_finrank

theorem eq_zero_of_preReflection_of_fixed_radical [FiniteDimensional K V]
    (B : V →ₗ[K] V →ₗ[K] W) (hB : B.IsAlt) (h2 : (2 : K) ≠ 0)
    (hdim : Module.finrank K V ≤ 3) (e : V) (α : V →ₗ[K] K) (hα : α e = 2)
    (hρ : ∀ u v, B (u - α u • e) (v - α v • e) = B u v)
    (x : V) (hx : x ≠ 0) (hfix : α x = 0) (hzero : B x = 0) : B = 0 := by
  classical
  have he : B e = 0 := apply_left_eq_zero_of_preReflection B hB h2 e α hα hρ
  let a : B.ker := ⟨e, he⟩
  let b : B.ker := ⟨x, hzero⟩
  have hab : LinearIndependent K ![a, b] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hv : s • e + t • x = 0 := congrArg (fun v : B.ker => (v : V)) hst
    have hscalar := congrArg α hv
    simp only [map_add, map_smul, hα, hfix, smul_eq_mul, mul_zero, add_zero,
      map_zero] at hscalar
    have hs : s = 0 := (mul_eq_zero.mp hscalar).resolve_right h2
    rw [hs, zero_smul, zero_add] at hv
    exact ⟨hs, (smul_eq_zero.mp hv).resolve_right hx⟩
  have hker : 2 ≤ Module.finrank K B.ker := by
    simpa using hab.fintype_card_le_finrank
  by_contra hne
  have hrange := two_le_finrank_range_of_isAlt B hB hne
  have hsum := LinearMap.finrank_range_add_finrank_ker B
  omega

end LinearMap.BilinMap

end
