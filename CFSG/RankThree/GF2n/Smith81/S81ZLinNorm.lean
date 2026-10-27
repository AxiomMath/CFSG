module

public import Mathlib.Tactic.Group
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

public section

namespace CFSG.RankThree.GF2n.Smith81.S81Z

variable {K : Type} [Field K] {Γ : Type} [Group Γ] {N : Type} [AddCommGroup N] [Module K N]
  [Module.Finite K N]

@[expose] def linNorm (u : N → Γ) (hu : Function.Injective u) : Subgroup Γ where
  carrier := {g | ∃ φ : N →ₗ[K] N, ∀ n, u (φ n) = g * u n * g⁻¹}
  mul_mem' := by
    rintro g h ⟨φ, hφ⟩ ⟨ψ, hψ⟩
    refine ⟨φ.comp ψ, fun n => ?_⟩
    rw [LinearMap.comp_apply, hφ, hψ]
    group
  one_mem' := ⟨LinearMap.id, fun n => by simp⟩
  inv_mem' := by
    rintro g ⟨φ, hφ⟩
    have hinj : Function.Injective φ := by
      intro n m h
      apply hu
      have h1 := hφ n
      have h2 := hφ m
      rw [h] at h1
      have h3 : g * u n * g⁻¹ = g * u m * g⁻¹ := h1.symm.trans h2
      simpa using h3
    let e : N ≃ₗ[K] N := LinearEquiv.ofInjectiveEndo φ hinj
    refine ⟨e.symm.toLinearMap, fun n => ?_⟩
    have h1 : u (φ (e.symm n)) = g * u (e.symm n) * g⁻¹ := hφ _
    have h2 : φ (e.symm n) = n := e.apply_symm_apply n
    rw [h2] at h1
    show u (e.symm n) = _
    rw [h1]
    group

variable (u : N → Γ) (hu : Function.Injective u)

include hu

noncomputable def linAdAux (g : ↥(linNorm (K := K) u hu)) : N ≃ₗ[K] N :=
  LinearEquiv.ofInjectiveEndo (Classical.choose g.2) (by
    intro n m h
    apply hu
    have h1 := Classical.choose_spec g.2 n
    have h2 := Classical.choose_spec g.2 m
    rw [h] at h1
    have h3 : (g : Γ) * u n * (g : Γ)⁻¹ = (g : Γ) * u m * (g : Γ)⁻¹ := h1.symm.trans h2
    simpa using h3)

theorem u_linAdAux (g : ↥(linNorm (K := K) u hu)) (n : N) :
    u (linAdAux u hu g n) = (g : Γ) * u n * (g : Γ)⁻¹ :=
  Classical.choose_spec g.2 n

noncomputable def linAd : ↥(linNorm (K := K) u hu) →* (N ≃ₗ[K] N) where
  toFun := linAdAux u hu
  map_one' := by
    refine LinearEquiv.ext fun n => hu ?_
    rw [u_linAdAux u hu 1 n]
    simp
  map_mul' g h := by
    refine LinearEquiv.ext fun n => hu ?_
    rw [u_linAdAux u hu (g * h) n, LinearEquiv.mul_apply, u_linAdAux u hu g, u_linAdAux u hu h n]
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group

theorem u_linAd (g : ↥(linNorm (K := K) u hu)) (n : N) :
    u (linAd u hu g n) = (g : Γ) * u n * (g : Γ)⁻¹ := u_linAdAux u hu g n

theorem linAd_eq {g : Γ} (hg : g ∈ linNorm (K := K) u hu) {φ : N →ₗ[K] N}
    (hφ : ∀ n, u (φ n) = g * u n * g⁻¹) (n : N) : linAd u hu ⟨g, hg⟩ n = φ n :=
  hu ((u_linAd u hu ⟨g, hg⟩ n).trans (hφ n).symm)

end CFSG.RankThree.GF2n.Smith81.S81Z
