module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.ZS.CommutingRefl
public import Mathlib.LinearAlgebra.Reflection

public section

namespace CFSG.StandardType.ZS

open Module

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

local instance (priority := high) zmodAddCommGroup : AddCommGroup (ZMod p) := Ring.toAddCommGroup

theorem conj_reflection (g : U ≃ₗ[ZMod p] U) {u : U} {φ : Dual (ZMod p) U}
    (h : φ u = 2) (h' : (φ ∘ₗ (g.symm : U →ₗ[ZMod p] U)) (g u) = 2) :
    g * Module.reflection h * g⁻¹ = Module.reflection h' := by
  ext y
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, Module.reflection_apply,
    Module.reflection_apply, LinearMap.comp_apply, map_sub, map_smul]
  simp only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply, LinearEquiv.coe_toLinearMap]

theorem mul_eq_four_of_reflection_eq {u v : U} {φ ψ : Dual (ZMod p) U}
    (hu : φ u = 2) (hv : ψ v = 2)
    (h : Module.reflection hu = Module.reflection hv) : φ v * ψ u = 4 := by
  have hvu : ψ u • v = (2 : ZMod p) • u := by
    have h1 : u - (2 : ZMod p) • u = u - ψ u • v := by
      simpa only [Module.reflection_apply, hu] using congrArg
        (fun e : U ≃ₗ[ZMod p] U => e u) h
    calc ψ u • v = u - (u - ψ u • v) := by module
      _ = u - (u - (2 : ZMod p) • u) := by rw [h1]
      _ = (2 : ZMod p) • u := by module
  calc φ v * ψ u = φ (ψ u • v) := by
        rw [LinearMap.map_smul φ (ψ u) v, smul_eq_mul, mul_comm]
    _ = φ ((2 : ZMod p) • u) := by rw [hvu]
    _ = 4 := by
        rw [LinearMap.map_smul φ (2 : ZMod p) u, hu, smul_eq_mul]
        norm_num

theorem eq_zero_of_orderOf_eq_two {u v : U} {φ ψ : Dual (ZMod p) U} (hp : p ≠ 2)
    (hu : φ u = 2) (hv : ψ v = 2)
    (h : orderOf (Module.reflection hu * Module.reflection hv) = 2) :
    φ v = 0 ∧ ψ u = 0 := by
  let ru : U ≃ₗ[ZMod p] U := Module.reflection hu
  let rv : U ≃ₗ[ZMod p] U := Module.reflection hv
  have hword : orderOf (ru * rv) = 2 := by simpa [ru, rv] using h
  have hw2 : (ru * rv) * (ru * rv) = 1 := by
    have := pow_orderOf_eq_one (ru * rv)
    rwa [hword, pow_two] at this
  have hwne : ru * rv ≠ 1 := by
    intro h1
    have : orderOf (ru * rv) = 1 := orderOf_eq_one_iff.mpr h1
    rw [hword] at this
    omega
  have hru : ru * ru = 1 := by
    dsimp only [ru]
    rw [← Module.reflection_inv hu]
    exact inv_mul_cancel _
  have hrv : rv * rv = 1 := by
    dsimp only [rv]
    rw [← Module.reflection_inv hv]
    exact inv_mul_cancel _
  have hcomm_eq : rv * ru = ru * rv := by
    have hru_inv : ru⁻¹ = ru := inv_eq_of_mul_eq_one_left hru
    have hrv_inv : rv⁻¹ = rv := inv_eq_of_mul_eq_one_left hrv
    calc rv * ru = rv⁻¹ * ru⁻¹ := by rw [hrv_inv, hru_inv]
      _ = (ru * rv)⁻¹ := by rw [mul_inv_rev]
      _ = ru * rv := by
          rw [← pow_two] at hw2
          exact inv_eq_of_mul_eq_one_left hw2
  have hcomm : Commute ru rv := (commute_iff_eq ru rv).mpr hcomm_eq.symm
  have hne : ru ≠ rv := by
    intro heq
    apply hwne
    calc ru * rv = rv * rv := by rw [heq]
      _ = 1 := hrv
  have h1 : φ v = 0 :=
    apply_eq_zero_of_commute hp (a := u) (b := v) (φ := φ) (ψ := ψ) hu hv hcomm hne
  have h2 : ψ u = 0 :=
    apply_eq_zero_of_commute hp (a := v) (b := u) (φ := ψ) (ψ := φ) hv hu hcomm.symm hne.symm
  exact ⟨h1, h2⟩

private theorem zrpo_pow_three_u_sub {u v : U} {φ ψ : Dual (ZMod p) U}
    (hu : φ u = 2) (hv : ψ v = 2)
    (h : (Module.reflection hu * Module.reflection hv)
        ((Module.reflection hu * Module.reflection hv)
          ((Module.reflection hu * Module.reflection hv) u)) = u) :
    (((φ v * ψ u - 1) * ((φ v * ψ u) ^ 2 - 4 * (φ v * ψ u) + 2)) • u
      - (ψ u * ((φ v * ψ u - 1) * (φ v * ψ u - 3))) • v) = 0 := by
  let w : U ≃ₗ[ZMod p] U := Module.reflection hu * Module.reflection hv
  have hwu : w u = (φ v * ψ u - 1) • u - ψ u • v := by
    dsimp only [w]
    rw [LinearEquiv.mul_apply, Module.reflection_apply, Module.reflection_apply]
    have hφ : φ (u - ψ u • v) = φ u - φ (ψ u • v) :=
      LinearMap.map_sub φ u (ψ u • v)
    rw [hφ, LinearMap.map_smul φ (ψ u) v, smul_eq_mul, hu]
    module
  have hwv : w v = φ v • u - v := by
    dsimp only [w]
    rw [LinearEquiv.mul_apply, Module.reflection_apply, Module.reflection_apply]
    have hφ : φ (v - ψ v • v) = φ v - φ (ψ v • v) :=
      LinearMap.map_sub φ v (ψ v • v)
    rw [hφ, LinearMap.map_smul φ (ψ v) v, smul_eq_mul, hv]
    module
  have hw2u : w (w u) = ((φ v * ψ u - 1) ^ 2 - φ v * ψ u) • u
      + (ψ u * (2 - φ v * ψ u)) • v := by
    rw [hwu]
    simp only [map_sub, map_smul]
    rw [hwu, hwv]
    module
  have hw2v : w (w v) = (φ v * (φ v * ψ u - 2)) • u + (1 - φ v * ψ u) • v := by
    rw [hwv]
    simp only [map_sub, map_smul]
    rw [hwu, hwv]
    module
  have hw3u : w (w (w u)) - u =
      ((φ v * ψ u - 1) * ((φ v * ψ u) ^ 2 - 4 * (φ v * ψ u) + 2)) • u
        - (ψ u * ((φ v * ψ u - 1) * (φ v * ψ u - 3))) • v := by
    rw [hw2u]
    simp only [map_add, map_smul]
    rw [hwu, hwv]
    module
  have h' : w (w (w u)) = u := by simpa [w] using h
  calc (((φ v * ψ u - 1) * ((φ v * ψ u) ^ 2 - 4 * (φ v * ψ u) + 2)) • u
      - (ψ u * ((φ v * ψ u - 1) * (φ v * ψ u - 3))) • v)
      = w (w (w u)) - u := hw3u.symm
    _ = 0 := by rw [h', sub_self]

private theorem zrpo_mul_eq_one_independent {u v : U} {φ ψ : Dual (ZMod p) U}
    (hp : p ≠ 2) (hu : φ u = 2)
    (hind : ¬ ∃ l : ZMod p, v = l • u)
    (hzero : (((φ v * ψ u - 1) * ((φ v * ψ u) ^ 2 - 4 * (φ v * ψ u) + 2)) • u
      - (ψ u * ((φ v * ψ u - 1) * (φ v * ψ u - 3))) • v) = 0) :
    φ v * ψ u = 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hu
    exact h2 hu.symm
  have hLI : LinearIndependent (ZMod p) ![u, v] := by
    rw [LinearIndependent.pair_iff' hu0]
    intro c hc
    exact hind ⟨c, hc.symm⟩
  have hzero' : ((φ v * ψ u - 1) * ((φ v * ψ u) ^ 2 - 4 * (φ v * ψ u) + 2)) • u
      + (-(ψ u * ((φ v * ψ u - 1) * (φ v * ψ u - 3)))) • v = 0 := by
    have h := hzero
    rw [sub_eq_add_neg, ← neg_smul] at h
    exact h
  obtain ⟨hA, hB⟩ := LinearIndependent.eq_zero_of_pair hLI hzero'
  have hB' : ψ u * ((φ v * ψ u - 1) * (φ v * ψ u - 3)) = 0 := neg_eq_zero.mp hB
  by_cases hs1 : φ v * ψ u - 1 = 0
  · exact sub_eq_zero.mp hs1
  · exfalso
    have hquad : (φ v * ψ u) ^ 2 - 4 * (φ v * ψ u) + 2 = 0 :=
      (mul_eq_zero.mp hA).resolve_left hs1
    have hfac : ψ u = 0 ∨ φ v * ψ u - 3 = 0 := by
      rw [← mul_assoc] at hB'
      rcases mul_eq_zero.mp hB' with hb | h3
      · exact Or.inl ((mul_eq_zero.mp hb).resolve_right hs1)
      · exact Or.inr h3
    rcases hfac with hb0 | hs3
    · have hs0 : φ v * ψ u = 0 := by rw [hb0, mul_zero]
      rw [hs0] at hquad
      have htwo : (2 : ZMod p) = 0 := by
        calc (2 : ZMod p) = 0 ^ 2 - 4 * 0 + 2 := by ring
          _ = 0 := hquad
      exact h2 htwo
    · have hs3' : φ v * ψ u = 3 := sub_eq_zero.mp hs3
      rw [hs3'] at hquad
      have hneg : (-1 : ZMod p) = 0 := by
        calc (-1 : ZMod p) = 3 ^ 2 - 4 * 3 + 2 := by ring_nf
          _ = 0 := hquad
      have hone : (1 : ZMod p) = 0 := neg_eq_zero.mp hneg
      have h2zero : (2 : ZMod p) = 0 := by
        calc (2 : ZMod p) = 1 + 1 := by ring
          _ = 0 + 0 := by rw [hone]
          _ = 0 := by ring
      exact h2 h2zero

private theorem zrpo_dependent_N_data {u v : U} {φ ψ : Dual (ZMod p) U}
    (hu : φ u = 2) (hv : ψ v = 2)
    (hdep : ∃ l : ZMod p, v = l • u) :
    ∃ N : U →ₗ[ZMod p] U,
      (∀ x, (Module.reflection hu * Module.reflection hv) x = x + N x) ∧
      (∀ x, N (N x) = 0) := by
  obtain ⟨l, hl⟩ := hdep
  let w : U ≃ₗ[ZMod p] U := Module.reflection hu * Module.reflection hv
  have hb : l * ψ u = 2 := by
    have := hv
    rw [hl, LinearMap.map_smul, smul_eq_mul] at this
    exact this
  have ha : φ v = 2 * l := by
    rw [hl, LinearMap.map_smul, smul_eq_mul, hu]
    ring
  let N : U →ₗ[ZMod p] U := (l • ψ + (-1 : ZMod p) • φ).smulRight u
  have hwN : ∀ x, w x = x + N x := by
    intro x
    dsimp only [w, N]
    simp only [LinearEquiv.mul_apply, Module.reflection_apply, hl, map_sub, map_smul,
      LinearMap.smulRight_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      smul_smul, hu]
    module
  have hNu : N u = 0 := by
    dsimp only [N]
    rw [LinearMap.smulRight_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    have hcoef : l * ψ u + (-1 : ZMod p) * φ u = 0 := by
      rw [hu, hb]
      norm_num
    rw [hcoef, zero_smul]
  have hN2 : ∀ x, N (N x) = 0 := by
    intro x
    have hx : N x = ((l • ψ + (-1 : ZMod p) • φ) x) • u := by
      dsimp only [N]
      rw [LinearMap.smulRight_apply]
    rw [hx, LinearMap.map_smul N ((l • ψ + (-1 : ZMod p) • φ) x) u, hNu, smul_zero]
  exact ⟨N, hwN, hN2⟩

private theorem zrpo_dependent_three {u v : U} {φ ψ : Dual (ZMod p) U}
    (hu : φ u = 2) (hv : ψ v = 2)
    (hdep : ∃ l : ZMod p, v = l • u)
    (h : orderOf (Module.reflection hu * Module.reflection hv) = 3) :
    (3 : ZMod p) = 0 := by
  obtain ⟨N, hwN, hN2⟩ := zrpo_dependent_N_data hu hv hdep
  let w : U ≃ₗ[ZMod p] U := Module.reflection hu * Module.reflection hv
  have hwN' : ∀ x, w x = x + N x := by simpa [w] using hwN
  have hword : orderOf w = 3 := by simpa [w] using h
  have hw3 : w ^ 3 = 1 := by
    rw [← hword]
    exact pow_orderOf_eq_one w
  have h3x : ∀ x, w (w (w x)) = x := by
    intro x
    have := congrArg (fun e : U ≃ₗ[ZMod p] U => e x) hw3
    simpa [pow_three, LinearEquiv.mul_apply] using this
  have hw2_apply : ∀ x, w (w x) = x + (2 : ZMod p) • N x := by
    intro x
    calc w (w x) = w x + N (w x) := hwN' _
      _ = (x + N x) + N (x + N x) := by rw [hwN']
      _ = (x + N x) + (N x + N (N x)) := by rw [LinearMap.map_add N x (N x)]
      _ = (x + N x) + (N x + 0) := by rw [hN2]
      _ = x + (2 : ZMod p) • N x := by module
  have hw3_apply : ∀ x, w (w (w x)) = x + (3 : ZMod p) • N x := by
    intro x
    calc w (w (w x)) = w (w x) + N (w (w x)) := hwN' _
      _ = (x + (2 : ZMod p) • N x) + N (x + (2 : ZMod p) • N x) := by rw [hw2_apply]
      _ = (x + (2 : ZMod p) • N x) + N x := by
          simp [hN2]
      _ = x + (3 : ZMod p) • N x := by
          module
  have h3N : ∀ x, (3 : ZMod p) • N x = 0 := by
    intro x
    have h1 : x + (3 : ZMod p) • N x = x := by
      rw [← hw3_apply x]
      exact h3x x
    have := congrArg (fun y : U => y - x) h1
    simpa using this
  have hthree : (3 : ZMod p) = 0 := by
    by_contra h3ne
    have hN0 : N = 0 := by
      ext x
      exact (smul_eq_zero.mp (h3N x)).resolve_left h3ne
    have hw1 : w = 1 := by
      ext x
      simp [hwN', hN0]
    have hone : orderOf w = 1 := orderOf_eq_one_iff.mpr hw1
    rw [hword] at hone
    omega
  exact hthree

private theorem zrpo_mul_eq_one_dependent {u v : U} {φ ψ : Dual (ZMod p) U}
    (hu : φ u = 2) (hv : ψ v = 2)
    (hdep : ∃ l : ZMod p, v = l • u)
    (h : orderOf (Module.reflection hu * Module.reflection hv) = 3) :
    φ v * ψ u = 1 := by
  obtain ⟨l, hl⟩ := hdep
  have hb : l * ψ u = 2 := by
    have := hv
    rw [hl, LinearMap.map_smul, smul_eq_mul] at this
    exact this
  have ha : φ v = 2 * l := by
    rw [hl, LinearMap.map_smul, smul_eq_mul, hu]
    ring
  have hs : φ v * ψ u = 4 := by
    rw [ha, mul_assoc, hb]
    norm_num
  have hthree : (3 : ZMod p) = 0 := zrpo_dependent_three hu hv ⟨l, hl⟩ h
  rw [hs]
  calc (4 : ZMod p) = 3 + 1 := by ring
    _ = 0 + 1 := by rw [hthree]
    _ = 1 := zero_add 1

theorem mul_eq_one_of_orderOf_eq_three {u v : U} {φ ψ : Dual (ZMod p) U}
    (hp : p ≠ 2) (hu : φ u = 2) (hv : ψ v = 2)
    (h : orderOf (Module.reflection hu * Module.reflection hv) = 3) :
    φ v * ψ u = 1 := by
  have hw3 : (Module.reflection hu * Module.reflection hv) ^ 3 = 1 := by
    rw [← h]
    exact pow_orderOf_eq_one _
  have h3u : (Module.reflection hu * Module.reflection hv)
      ((Module.reflection hu * Module.reflection hv)
        ((Module.reflection hu * Module.reflection hv) u)) = u := by
    have := congrArg (fun e : U ≃ₗ[ZMod p] U => e u) hw3
    simpa [pow_three, LinearEquiv.mul_apply] using this
  have hzero := zrpo_pow_three_u_sub hu hv h3u
  by_cases hdep : ∃ l : ZMod p, v = l • u
  · exact zrpo_mul_eq_one_dependent hu hv hdep h
  · exact zrpo_mul_eq_one_independent hp hu hdep hzero

end CFSG.StandardType.ZS
