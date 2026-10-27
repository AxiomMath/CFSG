module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import CFSG.RankThree.PartTwo.Sec16.Kcd166.KleinDim
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLineSum

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kcd166

open Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

private theorem eq_of_mem_ker_sub_one {u : Module.End K V} {v : V}
    (hv : v ∈ LinearMap.ker (u - 1)) : u v = v := by
  have h := LinearMap.mem_ker.1 hv
  rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h

private theorem neg_eq_of_mem_ker_add_one {u : Module.End K V} {v : V}
    (hv : v ∈ LinearMap.ker (u + 1)) : u v = -v := by
  have h := LinearMap.mem_ker.1 hv
  rwa [LinearMap.add_apply, Module.End.one_apply, add_eq_zero_iff_eq_neg] at h

private theorem mem_ker_sub_one_of_eq {u : Module.End K V} {v : V} (hv : u v = v) :
    v ∈ LinearMap.ker (u - 1) := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  exact hv

private theorem mem_ker_add_one_of_eq {u : Module.End K V} {v : V} (hv : u v = -v) :
    v ∈ LinearMap.ker (u + 1) := by
  rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, add_eq_zero_iff_eq_neg]
  exact hv

private theorem mapsTo_ker_sub_one {u q : Module.End K V} (h : u * q = q * u) :
    ∀ v ∈ LinearMap.ker (q - 1), u v ∈ LinearMap.ker (q - 1) := by
  intro v hv
  refine mem_ker_sub_one_of_eq ?_
  have hv' : q v = v := eq_of_mem_ker_sub_one hv
  rw [← Module.End.mul_apply, ← h, Module.End.mul_apply, hv']

private theorem finrank_eq_add_finrank_inf_ker_add_one [FiniteDimensional K V]
    (h2 : (2 : K) ≠ 0) {P : Submodule K V} {t : Module.End K V} (ht : t * t = 1)
    (hP : ∀ v ∈ P, t v ∈ P) :
    finrank K P = finrank K ↥(P ⊓ LinearMap.ker (t - 1)) +
      finrank K ↥(P ⊓ LinearMap.ker (t + 1)) := by
  have htv : ∀ v : V, t (t v) = v := by
    intro v
    rw [← Module.End.mul_apply, ht, Module.End.one_apply]
  have htwo : ∀ v : V, (2 : K) • v = v + v := fun v => two_smul K v
  have hsup : P ⊓ LinearMap.ker (t - 1) ⊔ P ⊓ LinearMap.ker (t + 1) = P := by
    refine le_antisymm (sup_le inf_le_left inf_le_left) ?_
    intro v hv
    have hP' : t v ∈ P := hP v hv
    have hv1 : (2 : K)⁻¹ • (v + t v) ∈ P ⊓ LinearMap.ker (t - 1) := by
      refine Submodule.mem_inf.2 ⟨P.smul_mem _ (P.add_mem hv hP'), ?_⟩
      refine mem_ker_sub_one_of_eq ?_
      rw [map_smul, map_add, htv, add_comm]
    have hv2 : (2 : K)⁻¹ • (v - t v) ∈ P ⊓ LinearMap.ker (t + 1) := by
      refine Submodule.mem_inf.2 ⟨P.smul_mem _ (P.sub_mem hv hP'), ?_⟩
      refine mem_ker_add_one_of_eq ?_
      rw [map_smul, map_sub, htv, ← smul_neg, neg_sub]
    have hsum : (2 : K)⁻¹ • (v + t v) + (2 : K)⁻¹ • (v - t v) = v := by
      rw [← smul_add, show v + t v + (v - t v) = (2 : K) • v by rw [htwo]; abel,
        smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [← hsum]
    exact Submodule.add_mem_sup hv1 hv2
  have hdisj : Disjoint (P ⊓ LinearMap.ker (t - 1)) (P ⊓ LinearMap.ker (t + 1)) := by
    rw [disjoint_iff, eq_bot_iff]
    intro v hv
    obtain ⟨h1, h2'⟩ := Submodule.mem_inf.1 hv
    rw [Submodule.mem_bot]
    have h3 : t v = v := eq_of_mem_ker_sub_one (Submodule.mem_inf.1 h1).2
    have h4 : t v = -v := neg_eq_of_mem_ker_add_one (Submodule.mem_inf.1 h2').2
    have h5 : v + v = 0 := eq_neg_iff_add_eq_zero.mp (h3.symm.trans h4)
    have h6 : (2 : K) • v = 0 := by rw [htwo, h5]
    exact (smul_eq_zero.mp h6).resolve_left h2
  have h := Submodule.finrank_sup_add_finrank_inf_eq (P ⊓ LinearMap.ker (t - 1))
    (P ⊓ LinearMap.ker (t + 1))
  rw [hsup, hdisj.eq_bot, finrank_bot, add_zero] at h
  exact h

private theorem finrank_eq_add_finrank_inf_ker_sq_add [FiniteDimensional K V]
    (h3 : (3 : K) ≠ 0) {P : Submodule K V} {β : Module.End K V} (hβ : β ^ 3 = 1)
    (hP : ∀ v ∈ P, β v ∈ P) :
    finrank K P = finrank K ↥(P ⊓ LinearMap.ker (β - 1)) +
      finrank K ↥(P ⊓ LinearMap.ker (β ^ 2 + β + 1)) := by
  let e : Module.End K V := β ^ 2 + β + 1
  have hev : ∀ v : V, e v = β (β v) + β v + v := by
    intro v
    have h : (β ^ 2 + β + 1 : Module.End K V) v = β (β v) + β v + v := by
      rw [LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply, pow_two,
        Module.End.mul_apply]
    exact h
  have hβ3v : ∀ v : V, β (β (β v)) = v := by
    intro v
    have h := congrArg (fun f : Module.End K V => f v) hβ
    simpa [pow_succ, pow_two, Module.End.mul_apply] using h
  have hthree : ∀ v : V, (3 : K) • v = v + v + v := by
    intro v
    rw [show (3 : K) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]
  have hβe : ∀ v : V, β (e v) = e v := by
    intro v
    rw [hev]
    rw [map_add, map_add, show β (β (β v)) = v from hβ3v v]
    abel
  have heP : ∀ v ∈ P, e v ∈ P := by
    intro v hv
    rw [hev]
    exact P.add_mem (P.add_mem (hP _ (hP v hv)) (hP v hv)) hv
  have hsq : ∀ v : V, e (e v) = (3 : K) • (e v) := by
    intro v
    set w : V := e v with hw
    have h1 : β w = w := by rw [hw]; exact hβe v
    have h2 : β (β w) = w := by rw [h1]; exact h1
    rw [hev w, h2, h1, hthree]
  have hsup : P ⊓ LinearMap.ker (β - 1) ⊔ P ⊓ LinearMap.ker (e) = P := by
    refine le_antisymm (sup_le inf_le_left inf_le_left) ?_
    intro v hv
    have hv1 : (3 : K)⁻¹ • (e v) ∈ P ⊓ LinearMap.ker (β - 1) := by
      refine Submodule.mem_inf.2 ⟨P.smul_mem _ (heP v hv), ?_⟩
      refine mem_ker_sub_one_of_eq ?_
      rw [map_smul, hβe]
    have hv2 : v - (3 : K)⁻¹ • (e v) ∈ P ⊓ LinearMap.ker (e) := by
      refine Submodule.mem_inf.2 ⟨P.sub_mem hv (P.smul_mem _ (heP v hv)), ?_⟩
      rw [LinearMap.mem_ker, map_sub, map_smul, hsq, smul_smul, inv_mul_cancel₀ h3, one_smul,
        sub_self]
    rw [show v = (3 : K)⁻¹ • (e v) + (v - (3 : K)⁻¹ • (e v)) from by abel]
    exact Submodule.add_mem_sup hv1 hv2
  have hdisj : Disjoint (P ⊓ LinearMap.ker (β - 1)) (P ⊓ LinearMap.ker (e)) := by
    rw [disjoint_iff, eq_bot_iff]
    intro v hv
    obtain ⟨h1, h2'⟩ := Submodule.mem_inf.1 hv
    rw [Submodule.mem_bot]
    have h4 : β v = v := eq_of_mem_ker_sub_one (Submodule.mem_inf.1 h1).2
    have h5 : e v = 0 := LinearMap.mem_ker.1 (Submodule.mem_inf.1 h2').2
    have h7 : e v = (3 : K) • v := by
      rw [hev, hthree, show β (β v) = v from by rw [h4, h4], h4]
    rw [h7] at h5
    exact (smul_eq_zero.mp h5).resolve_left h3
  have h := Submodule.finrank_sup_add_finrank_inf_eq (P ⊓ LinearMap.ker (β - 1))
    (P ⊓ LinearMap.ker (e))
  rw [hsup, hdisj.eq_bot, finrank_bot, add_zero] at h
  exact h

private theorem finrank_ker_sub_one_le_of_mul_cube [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    {s t x : Module.End K V} (hs : s * s = 1) (ht : t * t = 1) (hst : s * t = t * s)
    (hx3 : x * x * x = 1) (hxs : x * s = t * x) (hxt : x * t = s * t * x) :
    finrank K (LinearMap.ker (x - 1)) ≤ finrank K (LinearMap.ker (s - 1)) := by
  have hxs' : ∀ v : V, x (s v) = t (x v) := fun v => by
    have h := congrArg (fun f : Module.End K V => f v) hxs
    simpa [Module.End.mul_apply] using h
  have hxt' : ∀ v : V, x (t v) = s (t (x v)) := fun v => by
    have h := congrArg (fun f : Module.End K V => f v) hxt
    simpa [Module.End.mul_apply] using h
  have key1 : ∀ v : V, v ∈ LinearMap.ker (x - 1) → (1 + s) v = 0 → v = 0 := by
    intro v hv h0
    have hx : x v = v := eq_of_mem_ker_sub_one hv
    have hs1 : s v = -v := by
      have h : s v + v = 0 := by
        rw [add_comm]
        simpa [LinearMap.add_apply, Module.End.one_apply] using h0
      exact eq_neg_of_add_eq_zero_left h
    have htv' : t v = -v := by
      have h := hxs' v
      rw [hs1, map_neg, hx] at h
      exact h.symm
    have h1 : x (t v) = v := by
      rw [hxt' v, hx, htv', map_neg, hs1, neg_neg]
    have h2' : x (t v) = -v := by rw [htv', map_neg, hx]
    have h4 : v = -v := h1.symm.trans h2'
    have h5 : v + v = 0 := eq_neg_iff_add_eq_zero.mp h4
    have h6 : (2 : K) • v = 0 := by rw [two_smul, h5]
    exact (smul_eq_zero.mp h6).resolve_left h2
  have hinj1 : Function.Injective ((1 + s : Module.End K V).comp
      (LinearMap.ker (x - 1)).subtype) := by
    intro a b hab
    have h0 : ((1 + s : Module.End K V).comp (LinearMap.ker (x - 1)).subtype) (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    have h1 : ((a - b : ↥(LinearMap.ker (x - 1))) : V) = 0 := key1 _ (a - b).2 h0
    exact sub_eq_zero.mp (Subtype.ext h1)
  have h1 : finrank K ↥(LinearMap.ker (x - 1)) =
      finrank K (LinearMap.range ((1 + s : Module.End K V).comp
        (LinearMap.ker (x - 1)).subtype)) :=
    (LinearMap.finrank_range_of_inj hinj1).symm
  have h2' : finrank K (LinearMap.range ((1 + s : Module.End K V).comp
      (LinearMap.ker (x - 1)).subtype)) ≤ finrank K (LinearMap.ker (s - 1)) := by
    apply Submodule.finrank_mono
    rintro _ ⟨v, rfl⟩
    refine mem_ker_sub_one_of_eq ?_
    show s ((1 + s) (v : V)) = (1 + s) (v : V)
    rw [LinearMap.add_apply, Module.End.one_apply, map_add,
      show s (s (v : V)) = (v : V) from by rw [← Module.End.mul_apply, hs,
        Module.End.one_apply]]
    abel
  omega

private theorem injective_add_mul_sq (h2 : (2 : K) ≠ 0) {s t x : Module.End K V}
    (hs : s * s = 1) (hxs : x * s = t * x) (hxt : x * t = s * t * x) :
    ∀ v : V, v ∈ LinearMap.ker (s - 1) ⊓ LinearMap.ker (t + 1) →
      (1 + x + x * x) v = 0 → v = 0 := by
  have hxs' : ∀ v : V, x (s v) = t (x v) := fun v => by
    have h := congrArg (fun f : Module.End K V => f v) hxs
    simpa [Module.End.mul_apply] using h
  have hxt' : ∀ v : V, x (t v) = s (t (x v)) := fun v => by
    have h := congrArg (fun f : Module.End K V => f v) hxt
    simpa [Module.End.mul_apply] using h
  intro v hv h0
  obtain ⟨hP1, hP2⟩ := Submodule.mem_inf.1 hv
  have hsv : s v = v := eq_of_mem_ker_sub_one hP1
  have htv1 : t v = -v := neg_eq_of_mem_ker_add_one hP2
  have htv' : t (x v) = x v := by rw [← hxs' v, hsv]
  have hsx : s (x v) = -(x v) := by
    have h := hxt' v
    rw [htv1, map_neg, htv'] at h
    exact h.symm
  have htx2 : t (x (x v)) = -(x (x v)) := by
    have h := hxs' (x v)
    rw [hsx, map_neg] at h
    exact h.symm
  have hsx2 : s (x (x v)) = -(x (x v)) := by
    have h := hxt' (x v)
    rw [htv', htx2, map_neg] at h
    have h' : -(x (x v)) = s (x (x v)) := by simpa using congrArg Neg.neg h
    exact h'.symm
  have hstep1 : (1 - t : Module.End K V) ((1 + x + x * x) v) =
      (2 : K) • v + (2 : K) • (x (x v)) := by
    simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.one_apply, map_add,
      Module.End.mul_apply, htv1, htv', htx2]
    module
  have hstep2 : (1 + s : Module.End K V) ((2 : K) • v + (2 : K) • (x (x v))) =
      (4 : K) • v := by
    simp only [LinearMap.add_apply, Module.End.one_apply, map_add, map_smul, hsv, hsx2]
    module
  have hπ : ((1 + s : Module.End K V) * (1 - t)) ((1 + x + x * x) v) = (4 : K) • v := by
    rw [Module.End.mul_apply, hstep1, hstep2]
  rw [h0, map_zero] at hπ
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  exact (smul_eq_zero.mp hπ.symm).resolve_left h4

private theorem finrank_inf_ker_add_one_le_of_mul_cube [FiniteDimensional K V]
    (h2 : (2 : K) ≠ 0) {s t x : Module.End K V} (hs : s * s = 1) (ht : t * t = 1)
    (hst : s * t = t * s) (hx3 : x * x * x = 1) (hxs : x * s = t * x)
    (hxt : x * t = s * t * x) :
    finrank K ↥(LinearMap.ker (s - 1) ⊓ LinearMap.ker (t + 1)) ≤
      finrank K (LinearMap.ker (x - 1)) := by
  have hx3v : ∀ w : V, x (x (x w)) = w := by
    intro w
    have h := congrArg (fun f : Module.End K V => f w) hx3
    simpa [Module.End.mul_apply] using h
  let U : Submodule K V := LinearMap.ker (s - 1) ⊓ LinearMap.ker (t + 1)
  let φ : ↥U →ₗ[K] V := (1 + x + x * x).comp U.subtype
  have hinjφ : Function.Injective φ := by
    intro a b hab
    have h0 : φ (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h1 : ((a - b : ↥U) : V) = 0 :=
      injective_add_mul_sq h2 hs hxs hxt _ (a - b).2 h0
    exact sub_eq_zero.mp (Subtype.ext h1)
  have h1 : finrank K ↥U = finrank K (LinearMap.range φ) :=
    (LinearMap.finrank_range_of_inj hinjφ).symm
  have h2' : finrank K (LinearMap.range φ) ≤ finrank K (LinearMap.ker (x - 1)) := by
    apply Submodule.finrank_mono
    rintro _ ⟨v, rfl⟩
    refine mem_ker_sub_one_of_eq ?_
    show x ((1 + x + x * x) (v : V)) = (1 + x + x * x) (v : V)
    simp only [LinearMap.add_apply, Module.End.one_apply, map_add, Module.End.mul_apply]
    rw [hx3v]
    abel
  have hUle : finrank K ↥U ≤ finrank K (LinearMap.ker (x - 1)) := by
    omega
  exact hUle

theorem finrank_ker_sub_one_le_add_finrank_inf_of_mul_cube [FiniteDimensional K V]
    (h2 : (2 : K) ≠ 0) {s t x : Module.End K V} (hs : s * s = 1) (ht : t * t = 1)
    (hst : s * t = t * s) (hx3 : x * x * x = 1) (hxs : x * s = t * x)
    (hxt : x * t = s * t * x) :
    finrank K (LinearMap.ker (s - 1)) ≤
        finrank K (LinearMap.ker (x - 1)) +
          finrank K ↥(LinearMap.ker (s - 1) ⊓ LinearMap.ker (t - 1)) ∧
      finrank K (LinearMap.ker (x - 1)) ≤ finrank K (LinearMap.ker (s - 1)) := by
  have hsplit := finrank_eq_add_finrank_inf_ker_add_one (P := LinearMap.ker (s - 1)) h2 ht
    (mapsTo_ker_sub_one hst.symm)
  have hU := finrank_inf_ker_add_one_le_of_mul_cube h2 hs ht hst hx3 hxs hxt
  have hcx := finrank_ker_sub_one_le_of_mul_cube h2 hs ht hst hx3 hxs hxt
  exact ⟨by omega, hcx⟩

private theorem sq_apply {β : Module.End K V} (v : V) : (β ^ 2) v = β (β v) := by
  rw [pow_two, Module.End.mul_apply]

private theorem cube_apply {β : Module.End K V} (hβ : β ^ 3 = 1) (v : V) :
    β (β (β v)) = v := by
  have h := congrArg (fun f : Module.End K V => f v) hβ
  simpa [pow_succ, pow_two, Module.End.mul_apply] using h

private theorem norm_apply {β : Module.End K V} (v : V) :
    (β ^ 2 + β + 1 : Module.End K V) v = β (β v) + β v + v := by
  rw [LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply, sq_apply]

private theorem mapsTo_sub_sq {β : Module.End K V} (hβ : β ^ 3 = 1) {U : Submodule K V}
    (hβU : ∀ v ∈ U, β v ∈ U) :
    ∀ v ∈ U ⊓ LinearMap.ker (β ^ 2 + β + 1),
      (β - β ^ 2) v ∈ U ⊓ LinearMap.ker (β ^ 2 + β + 1) := by
  intro v hv
  obtain ⟨hvU, hvk⟩ := Submodule.mem_inf.1 hv
  have hβvU : β v ∈ U := hβU v hvU
  have hβ2vU : (β ^ 2) v ∈ U := by rw [sq_apply]; exact hβU _ hβvU
  refine Submodule.mem_inf.2 ⟨U.sub_mem hβvU hβ2vU, ?_⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, map_sub]
  have h1 : (β ^ 2 + β + 1 : Module.End K V) (β v) = v + β (β v) + β v := by
    rw [norm_apply, cube_apply hβ]
  have h2 : (β ^ 2 + β + 1 : Module.End K V) ((β ^ 2) v) = β v + v + β (β v) := by
    rw [norm_apply, sq_apply, cube_apply hβ, cube_apply hβ]
  rw [h1, h2]
  abel

private theorem injective_sub_sq (h3 : (3 : K) ≠ 0) {β : Module.End K V} (hβ : β ^ 3 = 1)
    {U : Submodule K V} :
    ∀ v ∈ U ⊓ LinearMap.ker (β ^ 2 + β + 1), (β - β ^ 2) v = 0 → v = 0 := by
  intro v hv h0
  have h0' : (β ^ 2 + β + 1 : Module.End K V) v = 0 :=
    LinearMap.mem_ker.1 (Submodule.mem_inf.1 hv).2
  have h1 : β v = (β ^ 2) v := by
    have h := h0
    rw [LinearMap.sub_apply, sub_eq_zero] at h
    exact h
  have h2 : β v = v := by
    have h3' : (β ^ 2) v = v := by
      rw [sq_apply]
      have h := congrArg (fun w => β w) h1
      rw [sq_apply, cube_apply hβ] at h
      exact h
    exact h1.trans h3'
  have h4 : v + v + v = 0 := by
    have h := h0'
    rw [norm_apply] at h
    rw [show β (β v) = v from by rw [h2, h2], h2] at h
    exact h
  have h6 : (3 : K) • v = 0 := by
    rw [show (3 : K) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]
    exact h4
  exact (smul_eq_zero.mp h6).resolve_left h3

private theorem sub_sq_neg {β s : Module.End K V} (hβ : β ^ 3 = 1) (hsβ : s * β = β ^ 2 * s) :
    (∀ v : V, s v = v → s ((β - β ^ 2) v) = -((β - β ^ 2) v)) ∧
      (∀ v : V, s v = -v → s ((β - β ^ 2) v) = (β - β ^ 2) v) := by
  have hsβv : ∀ w : V, s (β w) = (β ^ 2) (s w) := fun w => by
    have h := congrArg (fun f : Module.End K V => f w) hsβ
    simpa [Module.End.mul_apply] using h
  have hsβ2v : ∀ w : V, s ((β ^ 2) w) = β (s w) := by
    intro w
    rw [sq_apply]
    calc s (β (β w)) = (β ^ 2) (s (β w)) := hsβv (β w)
      _ = (β ^ 2) ((β ^ 2) (s w)) := by rw [hsβv w]
      _ = (β ^ 4) (s w) := by rw [← Module.End.mul_apply, ← pow_add]
      _ = β (s w) := by rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, hβ, one_mul]
  constructor
  · intro v hv
    rw [LinearMap.sub_apply, map_sub, hsβv v, hsβ2v v, hv, neg_sub]
  · intro v hv
    rw [LinearMap.sub_apply, map_sub, hsβv v, hsβ2v v, hv, map_neg, map_neg]
    abel

private theorem finrank_eigenspaces_eq [FiniteDimensional K V] {U' : Submodule K V}
    {D s : Module.End K V} (hDU' : ∀ v ∈ U', D v ∈ U') (hDinj : ∀ v ∈ U', D v = 0 → v = 0)
    (hanti1 : ∀ v ∈ U', s v = v → s (D v) = -(D v))
    (hanti2 : ∀ v ∈ U', s v = -v → s (D v) = D v) :
    finrank K ↥(U' ⊓ LinearMap.ker (s - 1)) =
      finrank K ↥(U' ⊓ LinearMap.ker (s + 1)) := by
  have key : ∀ A B : Submodule K V, A ≤ U' → (∀ v ∈ A, D v ∈ B) → finrank K ↥A ≤ finrank K ↥B := by
    intro A B hAU hAB
    have hinj : Function.Injective (D.comp A.subtype) := by
      intro a b hab
      have h0 : D.comp A.subtype (a - b) = 0 := by rw [map_sub, hab, sub_self]
      have hmem : ((a - b : ↥A) : V) ∈ U' := hAU (a - b).2
      have hzero : ((a - b : ↥A) : V) = 0 := hDinj _ hmem h0
      exact sub_eq_zero.mp (Subtype.ext hzero)
    have h1 : finrank K ↥A = finrank K (LinearMap.range (D.comp A.subtype)) :=
      (LinearMap.finrank_range_of_inj hinj).symm
    have h2 : finrank K (LinearMap.range (D.comp A.subtype)) ≤ finrank K ↥B := by
      apply Submodule.finrank_mono
      rintro _ ⟨v, rfl⟩
      exact hAB v v.2
    omega
  refine le_antisymm ?_ ?_
  · refine key (U' ⊓ LinearMap.ker (s - 1)) (U' ⊓ LinearMap.ker (s + 1)) inf_le_left ?_
    intro v hv
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hv
    refine Submodule.mem_inf.2 ⟨hDU' v h1, ?_⟩
    exact mem_ker_add_one_of_eq (hanti1 v h1 (eq_of_mem_ker_sub_one h2))
  · refine key (U' ⊓ LinearMap.ker (s + 1)) (U' ⊓ LinearMap.ker (s - 1)) inf_le_left ?_
    intro v hv
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hv
    refine Submodule.mem_inf.2 ⟨hDU' v h1, ?_⟩
    exact mem_ker_sub_one_of_eq (hanti2 v h1 (neg_eq_of_mem_ker_add_one h2))

private theorem mapsTo_inf_ker_sq_add {β s : Module.End K V} (hβ : β ^ 3 = 1)
    (hsβ : s * β = β ^ 2 * s) {U : Submodule K V} (hsU : ∀ v ∈ U, s v ∈ U) :
    ∀ v ∈ U ⊓ LinearMap.ker (β ^ 2 + β + 1),
      s v ∈ U ⊓ LinearMap.ker (β ^ 2 + β + 1) := by
  have hsβv : ∀ w : V, s (β w) = (β ^ 2) (s w) := fun w => by
    have h := congrArg (fun f : Module.End K V => f w) hsβ
    simpa [Module.End.mul_apply] using h
  have hsβ2v : ∀ w : V, s ((β ^ 2) w) = β (s w) := by
    intro w
    rw [sq_apply]
    calc s (β (β w)) = (β ^ 2) (s (β w)) := hsβv (β w)
      _ = (β ^ 2) ((β ^ 2) (s w)) := by rw [hsβv w]
      _ = (β ^ 4) (s w) := by rw [← Module.End.mul_apply, ← pow_add]
      _ = β (s w) := by rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, hβ, one_mul]
  intro v hv
  obtain ⟨hvU, hvk⟩ := Submodule.mem_inf.1 hv
  have h0 : (β ^ 2 + β + 1 : Module.End K V) v = 0 := LinearMap.mem_ker.1 hvk
  have hecomm : ∀ w : V, (β ^ 2 + β + 1 : Module.End K V) (s w) =
      s ((β ^ 2 + β + 1 : Module.End K V) w) := by
    intro w
    rw [norm_apply, norm_apply, ← sq_apply (s w), ← sq_apply w, map_add, map_add,
      (hsβv w).symm, (hsβ2v w).symm]
    abel
  refine Submodule.mem_inf.2 ⟨hsU v hvU, ?_⟩
  rw [LinearMap.mem_ker, hecomm, h0, map_zero]

private theorem even_finrank_inf_ker_sq_add [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    (h3 : (3 : K) ≠ 0) {β s : Module.End K V} (hβ : β ^ 3 = 1) (hs : s * s = 1)
    (hsβ : s * β = β ^ 2 * s) {U : Submodule K V} (hβU : ∀ v ∈ U, β v ∈ U)
    (hsU : ∀ v ∈ U, s v ∈ U) :
    Even (finrank K ↥(U ⊓ LinearMap.ker (β ^ 2 + β + 1))) := by
  have hDmem := mapsTo_sub_sq hβ hβU
  have hDinj := injective_sub_sq (K := K) h3 hβ (U := U)
  have hneg := sub_sq_neg (K := K) hβ hsβ
  have hfeq := finrank_eigenspaces_eq (U' := U ⊓ LinearMap.ker (β ^ 2 + β + 1))
    (D := β - β ^ 2) (s := s) hDmem hDinj (fun v _ hv => hneg.1 v hv)
    (fun v _ hv => hneg.2 v hv)
  have hcompl := finrank_eq_add_finrank_inf_ker_add_one
    (P := U ⊓ LinearMap.ker (β ^ 2 + β + 1)) h2 hs (mapsTo_inf_ker_sq_add hβ hsβ hsU)
  rw [hcompl, hfeq]
  exact ⟨_, rfl⟩

theorem even_finrank_sub_finrank_inf_ker_sub_one [FiniteDimensional K V]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {β s : Module.End K V} (hβ : β ^ 3 = 1)
    (hs : s * s = 1) (hsβ : s * β = β ^ 2 * s) {U : Submodule K V}
    (hβU : ∀ v ∈ U, β v ∈ U) (hsU : ∀ v ∈ U, s v ∈ U) :
    Even (finrank K U - finrank K ↥(U ⊓ LinearMap.ker (β - 1))) := by
  have hsplit := finrank_eq_add_finrank_inf_ker_sq_add h3 hβ hβU
  have heven := even_finrank_inf_ker_sq_add h2 h3 hβ hs hsβ hβU hsU
  obtain ⟨k, hk⟩ := heven
  have hdiff : finrank K U - finrank K ↥(U ⊓ LinearMap.ker (β - 1)) = k + k := by
    omega
  rw [hdiff]
  exact ⟨k, rfl⟩

theorem finrank_ker_sub_one_conj {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] (ρ : Representation K Γ W) (g a : Γ) :
    finrank K (LinearMap.ker (ρ (g * a * g⁻¹) - 1)) =
      finrank K (LinearMap.ker (ρ a - 1)) := by
  have hconj : ρ (g * a * g⁻¹) = ρ g * ρ a * ρ g⁻¹ := by rw [map_mul, map_mul]
  rw [hconj]
  let e : W ≃ₗ[K] W :=
    { toFun := ρ g
      invFun := ρ g⁻¹
      left_inv := fun w => by simp
      right_inv := fun w => by simp
      map_add' := map_add (ρ g)
      map_smul' := map_smul (ρ g) }
  have hmap : (LinearMap.ker (ρ a - 1)).map (ρ g) =
      LinearMap.ker (ρ g * ρ a * ρ g⁻¹ - 1) := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine mem_ker_sub_one_of_eq ?_
      have hv' : ρ a v = v := eq_of_mem_ker_sub_one hv
      rw [Module.End.mul_apply, Module.End.mul_apply, Representation.inv_self_apply, hv']
    · intro hw
      have hw' : (ρ g * ρ a * ρ g⁻¹) w = w := eq_of_mem_ker_sub_one hw
      have hmem : ρ g⁻¹ w ∈ LinearMap.ker (ρ a - 1) := by
        refine mem_ker_sub_one_of_eq ?_
        apply (ρ.apply_bijective g).1
        rw [Module.End.mul_apply, Module.End.mul_apply] at hw'
        calc ρ g (ρ a (ρ g⁻¹ w)) = (ρ g * ρ a * ρ g⁻¹) w := by
              rw [Module.End.mul_apply, Module.End.mul_apply]
          _ = w := hw'
          _ = ρ g (ρ g⁻¹ w) := (Representation.self_inv_apply ρ g w).symm
      exact ⟨ρ g⁻¹ w, hmem, Representation.self_inv_apply ρ g w⟩
  have hfin : finrank K ↥((LinearMap.ker (ρ a - 1)).map (ρ g)) =
      finrank K ↥(LinearMap.ker (ρ a - 1)) := by
    have hcoe : ((e : W →ₗ[K] W)) = ρ g := rfl
    rw [← hcoe]
    exact LinearEquiv.finrank_map_eq e (LinearMap.ker (ρ a - 1))
  rw [← hmap, hfin]

private theorem mem_alternating_two_swaps {a b c d : Fin 6} (hab : a ≠ b) (hcd : c ≠ d) :
    Equiv.swap a b * Equiv.swap c d ∈ alternatingGroup (Fin 6) :=
  Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
    (Equiv.Perm.swap_isSwap_iff.mpr hab) (Equiv.Perm.swap_isSwap_iff.mpr hcd)

private theorem mem_alternating_four_swaps {a b c d e f g h : Fin 6} (hab : a ≠ b) (hcd : c ≠ d)
    (hef : e ≠ f) (hgh : g ≠ h) :
    Equiv.swap a b * Equiv.swap c d * Equiv.swap e f * Equiv.swap g h ∈
      alternatingGroup (Fin 6) := by
  have h1 := mem_alternating_two_swaps (a := a) (b := b) (c := c) (d := d) hab hcd
  have h2 := mem_alternating_two_swaps (a := e) (b := f) (c := g) (d := h) hef hgh
  have h := (alternatingGroup (Fin 6)).mul_mem h1 h2
  simpa [mul_assoc] using h

private def t1 : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, mem_alternating_two_swaps (by decide) (by decide)⟩

private def t3 : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 3 * Equiv.swap 1 2, mem_alternating_two_swaps (by decide) (by decide)⟩

private def u1 : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 2 3 * Equiv.swap 4 5, mem_alternating_two_swaps (by decide) (by decide)⟩

private def x3 : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, mem_alternating_two_swaps (by decide) (by decide)⟩

private def y1 : alternatingGroup (Fin 6) :=
  ⟨(Equiv.swap 0 2 * Equiv.swap 2 4) * (Equiv.swap 1 3 * Equiv.swap 3 5), by
    have h1 := mem_alternating_two_swaps (a := (0 : Fin 6)) (b := 2) (c := 2) (d := 4)
      (by decide) (by decide)
    have h2 := mem_alternating_two_swaps (a := (1 : Fin 6)) (b := 3) (c := 3) (d := 5)
      (by decide) (by decide)
    exact (alternatingGroup (Fin 6)).mul_mem h1 h2⟩

private def b9 : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 3 4 * Equiv.swap 4 5, mem_alternating_two_swaps (by decide) (by decide)⟩

private def s9 : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 3 4, mem_alternating_two_swaps (by decide) (by decide)⟩

private def g1 : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 3 * Equiv.swap 3 1 * Equiv.swap 1 4 * Equiv.swap 2 5,
    mem_alternating_four_swaps (by decide) (by decide) (by decide) (by decide)⟩

private def g2 : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 2 5 * Equiv.swap 5 4,
    mem_alternating_four_swaps (by decide) (by decide) (by decide) (by decide)⟩

private def g3 : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 1 4 * Equiv.swap 4 3, mem_alternating_two_swaps (by decide) (by decide)⟩

private theorem t1_sq : t1 * t1 = 1 := by decide

private theorem t3_sq : t3 * t3 = 1 := by decide

private theorem u1_sq : u1 * u1 = 1 := by decide

private theorem y1_cube : y1 * y1 * y1 = 1 := by decide

private theorem b9_cube : b9 * b9 * b9 = 1 := by decide

private theorem s9_sq : s9 * s9 = 1 := by decide

private theorem x3_cube : x3 * x3 * x3 = 1 := by decide

private theorem t1_t3_comm : t1 * t3 = t3 * t1 := by decide

private theorem t1_u1_comm : t1 * u1 = u1 * t1 := by decide

private theorem x3_t1 : x3 * t1 = t3 * x3 := by decide

private theorem x3_t3 : x3 * t3 = t1 * t3 * x3 := by decide

private theorem y1_t1 : y1 * t1 = u1 * y1 := by decide

private theorem y1_u1 : y1 * u1 = (t1 * u1) * y1 := by decide

private theorem x3_b9_comm : x3 * b9 = b9 * x3 := by decide

private theorem s9_b9 : s9 * b9 = b9 ^ 2 * s9 := by decide

private theorem x3_s9 : x3 * s9 = s9 * x3 ^ 2 := by decide

private theorem x3b9_s9 : (x3 * b9) * s9 = s9 * (x3 * b9) ^ 2 := by decide

private theorem g1_conj : g1 * x3 * g1⁻¹ = b9 := by decide

private theorem g2_conj : g2 * (x3 * b9) * g2⁻¹ = y1 := by decide

private theorem g3_conj : g3 * (x3 ^ 2 * b9) * g3⁻¹ = y1 := by decide

private theorem t1_ne_one : t1 ≠ 1 := by decide

private theorem u1_ne_one : u1 ≠ 1 := by decide

private theorem t3_ne_one : t3 ≠ 1 := by decide

private theorem t1t3_sq : (t1 * t3) * (t1 * t3) = 1 := by decide

private theorem t1t3_ne_one : t1 * t3 ≠ 1 := by decide

private theorem t1u1_sq : (t1 * u1) * (t1 * u1) = 1 := by decide

private theorem t1u1_ne_one : t1 * u1 ≠ 1 := by decide

private theorem cycleType_eq_two_two {t : Equiv.Perm (Fin 6)} (ht : t ∈ alternatingGroup (Fin 6))
    (hsq : t * t = 1) (hne : t ≠ 1) : t.cycleType = {2, 2} := by
  have h2 : t ^ 2 = 1 := by rwa [pow_two]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : t.cycleType = Multiset.replicate t.cycleType.card 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one h2
  have hpos : 0 < t.cycleType.card := by
    rw [Equiv.Perm.card_cycleType_pos]
    exact hne
  have hsum : t.cycleType.sum = 2 * t.cycleType.card := by
    rw [hcyc, Multiset.sum_replicate, Multiset.card_replicate, nsmul_eq_mul,
      Nat.cast_id]
    omega
  have hsign : Equiv.Perm.sign t = 1 := Equiv.Perm.mem_alternatingGroup.1 ht
  rw [Equiv.Perm.sign_of_cycleType, hsum] at hsign
  have heven : Even (2 * t.cycleType.card + t.cycleType.card) :=
    (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)).1 hsign
  have hle : t.cycleType.card ≤ 3 := by
    have h := t.sum_cycleType_le
    rw [hsum] at h
    simp at h
    omega
  have hcard : t.cycleType.card = 2 := by
    obtain ⟨k, hk⟩ := heven
    omega
  rw [hcard] at hcyc
  simpa using hcyc

private theorem exists_conj_eq_t1 {u : alternatingGroup (Fin 6)} (hu2 : u * u = 1)
    (hu1 : u ≠ 1) : ∃ g : alternatingGroup (Fin 6), g * u * g⁻¹ = t1 := by
  have hsq : (u : Equiv.Perm (Fin 6)) * (u : Equiv.Perm (Fin 6)) = 1 := by
    simpa using congrArg Subtype.val hu2
  have hne : (u : Equiv.Perm (Fin 6)) ≠ 1 := by
    intro h
    exact hu1 (Subtype.ext h)
  have hcyc : (u : Equiv.Perm (Fin 6)).cycleType = {2, 2} :=
    cycleType_eq_two_two u.2 hsq hne
  have hcyc1 : (t1 : Equiv.Perm (Fin 6)).cycleType = {2, 2} := by
    have h := Equiv.Perm.cycleType_swap_mul_swap_of_nodup (x := (0 : Fin 6)) (y := 1) (z := 2)
      (t := 3) (by decide)
    simpa [t1] using h
  have hconj : IsConj (u : Equiv.Perm (Fin 6)) (t1 : Equiv.Perm (Fin 6)) := by
    rw [Equiv.Perm.isConj_iff_cycleType_eq, hcyc, hcyc1]
  have hsupp : (u : Equiv.Perm (Fin 6)).support.card + 2 ≤ Fintype.card (Fin 6) := by
    have hsum : (u : Equiv.Perm (Fin 6)).cycleType.sum = 4 := by
      rw [hcyc]
      simp
    have hcard : (u : Equiv.Perm (Fin 6)).support.card = 4 := by
      rw [← Equiv.Perm.sum_cycleType]
      exact hsum
    rw [hcard]
    simp
  obtain ⟨g, hg⟩ := alternatingGroup.isConj_of hconj hsupp
  refine ⟨g, ?_⟩
  have hg' : (↑g : alternatingGroup (Fin 6)) * u = t1 * (↑g : alternatingGroup (Fin 6)) := hg
  have hg'' : (↑↑g : Equiv.Perm (Fin 6)) * (↑u : Equiv.Perm (Fin 6)) =
      (↑t1 : Equiv.Perm (Fin 6)) * (↑↑g : Equiv.Perm (Fin 6)) := congrArg Subtype.val hg'
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hg'']
  group

private theorem three_le_of_dims {f a n c1 c2 e k l : ℕ}
    (hdim1 : n + 2 * a = 3 * f) (haf : a ≤ f) (hm : 1 ≤ f - a)
    (hf1 : f ≤ c1 + a) (hc1f : c1 ≤ f) (hf2 : f ≤ c2 + a) (hc2f : c2 ≤ f)
    (hE9 : n + 3 * e = 2 * c1 + 2 * c2) (hec1 : e ≤ c1)
    (hk : c1 - e = k + k) (hl : c2 - e = l + l) : 3 ≤ f := by
  omega

private theorem finrank_ker_sub_one_eq_t1 {K : Type*} [Field K] {W : Type*} [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] (ρ : Representation K (alternatingGroup (Fin 6)) W)
    {u : alternatingGroup (Fin 6)} (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    Module.finrank K (LinearMap.ker (ρ u - 1)) =
      Module.finrank K (LinearMap.ker (ρ t1 - 1)) := by
  obtain ⟨g, hg⟩ := exists_conj_eq_t1 hu2 hu1
  rw [← hg]
  exact (finrank_ker_sub_one_conj ρ g u).symm

private theorem dim_four_group_t1_t3 {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {W : Type*}
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ρ : Representation K (alternatingGroup (Fin 6)) W) :
    Module.finrank K W + 2 * Module.finrank K ↥(LinearMap.ker (ρ t1 - 1) ⊓
        LinearMap.ker (ρ t3 - 1)) = 3 * Module.finrank K (LinearMap.ker (ρ t1 - 1)) := by
  have h := finrank_add_two_mul_finrank_inf (𝕜 := K) (V := W) h2
    (by simpa [map_mul] using congrArg ρ t1_sq)
    (by simpa [map_mul] using congrArg ρ t3_sq)
    (by simpa [map_mul] using congrArg ρ t1_t3_comm)
  have h3 : Module.finrank K (LinearMap.ker (ρ t3 - 1)) =
      Module.finrank K (LinearMap.ker (ρ t1 - 1)) :=
    finrank_ker_sub_one_eq_t1 ρ t3_sq t3_ne_one
  have ht : Module.finrank K (LinearMap.ker (ρ (t1 * t3) - 1)) =
      Module.finrank K (LinearMap.ker (ρ t1 - 1)) :=
    finrank_ker_sub_one_eq_t1 ρ t1t3_sq t1t3_ne_one
  have hpr : Module.finrank K (LinearMap.ker (ρ t1 * ρ t3 - 1)) =
      Module.finrank K (LinearMap.ker (ρ (t1 * t3) - 1)) := by
    rw [show ρ t1 * ρ t3 = ρ (t1 * t3) from (map_mul ρ t1 t3).symm]
  rw [hpr, ht, h3] at h
  omega

private theorem le_add_inf_t1_t3_x3 {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {W : Type*}
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ρ : Representation K (alternatingGroup (Fin 6)) W) :
    Module.finrank K (LinearMap.ker (ρ t1 - 1)) ≤
        Module.finrank K (LinearMap.ker (ρ x3 - 1)) +
          Module.finrank K ↥(LinearMap.ker (ρ t1 - 1) ⊓ LinearMap.ker (ρ t3 - 1)) ∧
      Module.finrank K (LinearMap.ker (ρ x3 - 1)) ≤
        Module.finrank K (LinearMap.ker (ρ t1 - 1)) :=
  finrank_ker_sub_one_le_add_finrank_inf_of_mul_cube (K := K) (V := W) h2
    (by simpa [map_mul] using congrArg ρ t1_sq)
    (by simpa [map_mul] using congrArg ρ t3_sq)
    (by simpa [map_mul] using congrArg ρ t1_t3_comm)
    (by simpa [map_mul] using congrArg ρ x3_cube)
    (by simpa [map_mul] using congrArg ρ x3_t1)
    (by simpa [map_mul] using congrArg ρ x3_t3)

private theorem one_le_sub_t1_t3 {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {W : Type*}
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ρ : Representation K (alternatingGroup (Fin 6)) W) (hρ : ρ ≠ 1) :
    1 ≤ Module.finrank K (LinearMap.ker (ρ t1 - 1)) -
      Module.finrank K ↥(LinearMap.ker (ρ t1 - 1) ⊓ LinearMap.ker (ρ t3 - 1)) := by
  set a : ℕ := Module.finrank K ↥(LinearMap.ker (ρ t1 - 1) ⊓ LinearMap.ker (ρ t3 - 1)) with ha
  set f : ℕ := Module.finrank K (LinearMap.ker (ρ t1 - 1)) with hf
  have haf : a ≤ f := by
    rw [ha, hf]
    exact Submodule.finrank_mono inf_le_left
  have hdim : Module.finrank K W + 2 * a = 3 * f := by
    have h := dim_four_group_t1_t3 h2 ρ
    rw [← ha, ← hf] at h
    exact h
  by_contra hlt
  rw [not_le, Nat.lt_one_iff] at hlt
  have hae : a = f := by omega
  have hnf : Module.finrank K W = f := by omega
  have htop : LinearMap.ker (ρ t1 - 1) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← hf, hnf]
  have hρ1 : ρ t1 = 1 := by
    ext v
    have hv : v ∈ LinearMap.ker (ρ t1 - 1) := by rw [htop]; trivial
    simpa using eq_of_mem_ker_sub_one hv
  have hker : t1 ∈ ρ.ker := by
    rw [MonoidHom.mem_ker]
    exact hρ1
  have hbot : ρ.ker ≠ ⊥ := by
    intro hbot'
    rw [hbot'] at hker
    exact t1_ne_one (Subgroup.mem_bot.1 hker)
  have htop' : ρ.ker = ⊤ := by
    rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (α := Fin 6) (by simp)
      (N := ρ.ker) with h | h
    · exact absurd h hbot
    · exact h
  exact hρ (MonoidHom.ker_eq_top_iff.mp htop')

private theorem dim_four_group_t1_u1 {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {W : Type*}
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ρ : Representation K (alternatingGroup (Fin 6)) W) :
    Module.finrank K W + 2 * Module.finrank K ↥(LinearMap.ker (ρ t1 - 1) ⊓
        LinearMap.ker (ρ u1 - 1)) = 3 * Module.finrank K (LinearMap.ker (ρ t1 - 1)) := by
  have h := finrank_add_two_mul_finrank_inf (𝕜 := K) (V := W) h2
    (by simpa [map_mul] using congrArg ρ t1_sq)
    (by simpa [map_mul] using congrArg ρ u1_sq)
    (by simpa [map_mul] using congrArg ρ t1_u1_comm)
  have h3 : Module.finrank K (LinearMap.ker (ρ u1 - 1)) =
      Module.finrank K (LinearMap.ker (ρ t1 - 1)) :=
    finrank_ker_sub_one_eq_t1 ρ u1_sq u1_ne_one
  have ht : Module.finrank K (LinearMap.ker (ρ (t1 * u1) - 1)) =
      Module.finrank K (LinearMap.ker (ρ t1 - 1)) :=
    finrank_ker_sub_one_eq_t1 ρ t1u1_sq t1u1_ne_one
  have hpr : Module.finrank K (LinearMap.ker (ρ t1 * ρ u1 - 1)) =
      Module.finrank K (LinearMap.ker (ρ (t1 * u1) - 1)) := by
    rw [show ρ t1 * ρ u1 = ρ (t1 * u1) from (map_mul ρ t1 u1).symm]
  rw [hpr, ht, h3] at h
  omega

private theorem inf_t1_u1_eq_inf_t1_t3 {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {W : Type*}
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ρ : Representation K (alternatingGroup (Fin 6)) W) :
    Module.finrank K ↥(LinearMap.ker (ρ t1 - 1) ⊓ LinearMap.ker (ρ u1 - 1)) =
      Module.finrank K ↥(LinearMap.ker (ρ t1 - 1) ⊓ LinearMap.ker (ρ t3 - 1)) := by
  have h1 := dim_four_group_t1_t3 h2 ρ
  have h2' := dim_four_group_t1_u1 h2 ρ
  omega

private theorem le_add_inf_t1_u1_y1 {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {W : Type*}
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ρ : Representation K (alternatingGroup (Fin 6)) W) :
    Module.finrank K (LinearMap.ker (ρ t1 - 1)) ≤
        Module.finrank K (LinearMap.ker (ρ y1 - 1)) +
          Module.finrank K ↥(LinearMap.ker (ρ t1 - 1) ⊓ LinearMap.ker (ρ u1 - 1)) ∧
      Module.finrank K (LinearMap.ker (ρ y1 - 1)) ≤
        Module.finrank K (LinearMap.ker (ρ t1 - 1)) :=
  finrank_ker_sub_one_le_add_finrank_inf_of_mul_cube (K := K) (V := W) h2
    (by simpa [map_mul] using congrArg ρ t1_sq)
    (by simpa [map_mul] using congrArg ρ u1_sq)
    (by simpa [map_mul] using congrArg ρ t1_u1_comm)
    (by simpa [map_mul] using congrArg ρ y1_cube)
    (by simpa [map_mul] using congrArg ρ y1_t1)
    (by simpa [map_mul] using congrArg ρ y1_u1)

private theorem line_sum_t1 {K : Type*} [Field K] (h3 : (3 : K) ≠ 0) {W : Type*}
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ρ : Representation K (alternatingGroup (Fin 6)) W) :
    Module.finrank K W + 3 * Module.finrank K ↥(LinearMap.ker (ρ x3 - 1) ⊓
        LinearMap.ker (ρ b9 - 1)) =
      2 * Module.finrank K (LinearMap.ker (ρ x3 - 1)) +
        2 * Module.finrank K (LinearMap.ker (ρ y1 - 1)) := by
  have hb9 : Module.finrank K (LinearMap.ker (ρ b9 - 1)) =
      Module.finrank K (LinearMap.ker (ρ x3 - 1)) := by
    have h := finrank_ker_sub_one_conj ρ g1 x3
    rw [g1_conj] at h
    exact h
  have hz1 : Module.finrank K (LinearMap.ker (ρ (x3 * b9) - 1)) =
      Module.finrank K (LinearMap.ker (ρ y1 - 1)) := by
    have h := finrank_ker_sub_one_conj ρ g2 (x3 * b9)
    rw [g2_conj] at h
    exact h.symm
  have hz2 : Module.finrank K (LinearMap.ker (ρ (x3 ^ 2 * b9) - 1)) =
      Module.finrank K (LinearMap.ker (ρ y1 - 1)) := by
    have h := finrank_ker_sub_one_conj ρ g3 (x3 ^ 2 * b9)
    rw [g3_conj] at h
    exact h.symm
  have h := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.finrank_lineSum (K := K) (V := W)
    h3 (by simpa [map_mul, pow_three'] using congrArg ρ x3_cube)
    (by simpa [map_mul, pow_three'] using congrArg ρ b9_cube) (by
      show ρ x3 * ρ b9 = ρ b9 * ρ x3
      simpa [map_mul] using congrArg ρ x3_b9_comm)
  have hpr : Module.finrank K (LinearMap.ker (ρ x3 * ρ b9 - 1)) =
      Module.finrank K (LinearMap.ker (ρ (x3 * b9) - 1)) := by
    rw [show ρ x3 * ρ b9 = ρ (x3 * b9) from (map_mul ρ x3 b9).symm]
  have hpr2 : Module.finrank K (LinearMap.ker (ρ x3 ^ 2 * ρ b9 - 1)) =
      Module.finrank K (LinearMap.ker (ρ (x3 ^ 2 * b9) - 1)) := by
    rw [show ρ x3 ^ 2 = ρ (x3 ^ 2) from (map_pow ρ x3 2).symm,
      show ρ (x3 ^ 2) * ρ b9 = ρ (x3 ^ 2 * b9) from (map_mul ρ (x3 ^ 2) b9).symm]
  have h' : Module.finrank K (LinearMap.ker (ρ x3 - 1)) +
      Module.finrank K (LinearMap.ker (ρ b9 - 1)) +
      Module.finrank K (LinearMap.ker (ρ x3 * ρ b9 - 1)) +
      Module.finrank K (LinearMap.ker (ρ x3 ^ 2 * ρ b9 - 1)) =
      Module.finrank K W + 3 * Module.finrank K ↥(LinearMap.ker (ρ x3 - 1) ⊓
        LinearMap.ker (ρ b9 - 1)) := h
  rw [hpr, hpr2, hb9, hz1, hz2] at h'
  omega

private theorem even_sub_line_sum_t1 {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (h3 : (3 : K) ≠ 0) {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ρ : Representation K (alternatingGroup (Fin 6)) W) :
    Even (Module.finrank K (LinearMap.ker (ρ x3 - 1)) -
      Module.finrank K ↥(LinearMap.ker (ρ x3 - 1) ⊓ LinearMap.ker (ρ b9 - 1))) := by
  have hβU : ∀ v ∈ LinearMap.ker (ρ x3 - 1), ρ b9 v ∈ LinearMap.ker (ρ x3 - 1) := by
    intro v hv
    refine mem_ker_sub_one_of_eq ?_
    have hv' : ρ x3 v = v := eq_of_mem_ker_sub_one hv
    have hc : ρ x3 * ρ b9 = ρ b9 * ρ x3 := by
      simpa [map_mul] using congrArg ρ x3_b9_comm
    calc ρ x3 (ρ b9 v) = (ρ x3 * ρ b9) v := by rw [Module.End.mul_apply]
      _ = (ρ b9 * ρ x3) v := by rw [hc]
      _ = ρ b9 (ρ x3 v) := by rw [Module.End.mul_apply]
      _ = ρ b9 v := by rw [hv']
  have hsU : ∀ v ∈ LinearMap.ker (ρ x3 - 1), ρ s9 v ∈ LinearMap.ker (ρ x3 - 1) := by
    intro v hv
    refine mem_ker_sub_one_of_eq ?_
    have hv' : ρ x3 v = v := eq_of_mem_ker_sub_one hv
    have hv2 : (ρ x3 ^ 2) v = v := by rw [pow_two, Module.End.mul_apply, hv', hv']
    have hc : ρ x3 * ρ s9 = ρ s9 * ρ x3 ^ 2 := by
      simpa [map_mul, map_pow] using congrArg ρ x3_s9
    calc ρ x3 (ρ s9 v) = (ρ x3 * ρ s9) v := by rw [Module.End.mul_apply]
      _ = (ρ s9 * ρ x3 ^ 2) v := by rw [hc]
      _ = ρ s9 ((ρ x3 ^ 2) v) := by rw [Module.End.mul_apply]
      _ = ρ s9 v := by rw [hv2]
  exact even_finrank_sub_finrank_inf_ker_sub_one (K := K) (V := W) h2 h3
    (by simpa [map_mul, pow_three'] using congrArg ρ b9_cube)
    (by simpa [map_mul] using congrArg ρ s9_sq)
    (by simpa [map_mul, map_pow] using congrArg ρ s9_b9) hβU hsU

private theorem even_sub_line_sum_t1u1 {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (h3 : (3 : K) ≠ 0) {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ρ : Representation K (alternatingGroup (Fin 6)) W) :
    Even (Module.finrank K (LinearMap.ker (ρ (x3 * b9) - 1)) -
      Module.finrank K ↥(LinearMap.ker (ρ (x3 * b9) - 1) ⊓ LinearMap.ker (ρ b9 - 1))) := by
  have hβU : ∀ v ∈ LinearMap.ker (ρ (x3 * b9) - 1),
      ρ b9 v ∈ LinearMap.ker (ρ (x3 * b9) - 1) := by
    intro v hv
    refine mem_ker_sub_one_of_eq ?_
    have hv' : ρ (x3 * b9) v = v := eq_of_mem_ker_sub_one hv
    have hcomm : ρ (x3 * b9) * ρ b9 = ρ b9 * ρ (x3 * b9) := by
      rw [show ρ (x3 * b9) = ρ x3 * ρ b9 from map_mul ρ x3 b9]
      have hc : ρ x3 * ρ b9 = ρ b9 * ρ x3 := by
        simpa [map_mul] using congrArg ρ x3_b9_comm
      calc (ρ x3 * ρ b9) * ρ b9 = (ρ b9 * ρ x3) * ρ b9 := by rw [hc]
        _ = ρ b9 * (ρ x3 * ρ b9) := by rw [mul_assoc]
    calc ρ (x3 * b9) (ρ b9 v) = (ρ (x3 * b9) * ρ b9) v := by rw [Module.End.mul_apply]
      _ = (ρ b9 * ρ (x3 * b9)) v := by rw [hcomm]
      _ = ρ b9 (ρ (x3 * b9) v) := by rw [Module.End.mul_apply]
      _ = ρ b9 v := by rw [hv']
  have hsU : ∀ v ∈ LinearMap.ker (ρ (x3 * b9) - 1),
      ρ s9 v ∈ LinearMap.ker (ρ (x3 * b9) - 1) := by
    intro v hv
    refine mem_ker_sub_one_of_eq ?_
    have hv' : ρ (x3 * b9) v = v := eq_of_mem_ker_sub_one hv
    have hv2 : (ρ (x3 * b9) ^ 2) v = v := by
      rw [pow_two, Module.End.mul_apply, hv', hv']
    have hc : ρ (x3 * b9) * ρ s9 = ρ s9 * ρ (x3 * b9) ^ 2 := by
      simpa [map_mul, map_pow] using congrArg ρ x3b9_s9
    calc ρ (x3 * b9) (ρ s9 v) = (ρ (x3 * b9) * ρ s9) v := by rw [Module.End.mul_apply]
      _ = (ρ s9 * ρ (x3 * b9) ^ 2) v := by rw [hc]
      _ = ρ s9 ((ρ (x3 * b9) ^ 2) v) := by rw [Module.End.mul_apply]
      _ = ρ s9 v := by rw [hv2]
  exact even_finrank_sub_finrank_inf_ker_sub_one (K := K) (V := W) h2 h3
    (by simpa [map_mul, pow_three'] using congrArg ρ b9_cube)
    (by simpa [map_mul] using congrArg ρ s9_sq)
    (by simpa [map_mul, map_pow] using congrArg ρ s9_b9) hβU hsU

private theorem finrank_ker_x3b9 {K : Type*} [Field K] {W : Type*} [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] (ρ : Representation K (alternatingGroup (Fin 6)) W) :
    Module.finrank K (LinearMap.ker (ρ (x3 * b9) - 1)) =
      Module.finrank K (LinearMap.ker (ρ y1 - 1)) := by
  have hc := finrank_ker_sub_one_conj ρ g2 (x3 * b9)
  rw [g2_conj] at hc
  exact hc.symm

private theorem inf_ker_x3b9 {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
    (ρ : Representation K (alternatingGroup (Fin 6)) W) :
    LinearMap.ker (ρ (x3 * b9) - 1) ⊓ LinearMap.ker (ρ b9 - 1) =
      LinearMap.ker (ρ x3 - 1) ⊓ LinearMap.ker (ρ b9 - 1) := by
  ext w
  constructor
  · rintro ⟨h1, h2'⟩
    have h1' : ρ (x3 * b9) w = w := eq_of_mem_ker_sub_one h1
    have h2'' : ρ b9 w = w := eq_of_mem_ker_sub_one h2'
    refine Submodule.mem_inf.2 ⟨mem_ker_sub_one_of_eq ?_, h2'⟩
    rw [map_mul, Module.End.mul_apply, h2''] at h1'
    exact h1'
  · rintro ⟨h1, h2'⟩
    refine Submodule.mem_inf.2 ⟨mem_ker_sub_one_of_eq ?_, h2'⟩
    have h1' : ρ x3 w = w := eq_of_mem_ker_sub_one h1
    have h2'' : ρ b9 w = w := eq_of_mem_ker_sub_one h2'
    rw [map_mul, Module.End.mul_apply, h2'', h1']

private theorem three_le_finrank_ker_sub_one_t1 {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (h3 : (3 : K) ≠ 0) {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (ρ : Representation K (alternatingGroup (Fin 6)) W) (hρ : ρ ≠ 1) :
    3 ≤ Module.finrank K (LinearMap.ker (ρ t1 - 1)) := by
  set f : ℕ := Module.finrank K (LinearMap.ker (ρ t1 - 1)) with hf
  set n : ℕ := Module.finrank K W with hn
  set a : ℕ := Module.finrank K ↥(LinearMap.ker (ρ t1 - 1) ⊓ LinearMap.ker (ρ t3 - 1)) with ha
  set a' : ℕ := Module.finrank K ↥(LinearMap.ker (ρ t1 - 1) ⊓ LinearMap.ker (ρ u1 - 1)) with ha'
  set c1 : ℕ := Module.finrank K (LinearMap.ker (ρ x3 - 1)) with hc1
  set c2 : ℕ := Module.finrank K (LinearMap.ker (ρ y1 - 1)) with hc2
  set e : ℕ := Module.finrank K ↥(LinearMap.ker (ρ x3 - 1) ⊓ LinearMap.ker (ρ b9 - 1)) with he
  have hdim1 : n + 2 * a = 3 * f := by
    rw [hn, ha, hf]
    exact dim_four_group_t1_t3 h2 ρ
  have haf : a ≤ f := by
    rw [ha, hf]
    exact Submodule.finrank_mono inf_le_left
  have hm : 1 ≤ f - a := by
    rw [hf, ha]
    exact one_le_sub_t1_t3 h2 ρ hρ
  have hL1 := le_add_inf_t1_t3_x3 h2 ρ
  have hf1 : f ≤ c1 + a := by
    have h := hL1.1
    rw [← hf, ← hc1, ← ha] at h
    omega
  have hc1f : c1 ≤ f := by
    have h := hL1.2
    rw [← hf, ← hc1] at h
    exact h
  have haa' : a' = a := by
    rw [ha', ha]
    exact inf_t1_u1_eq_inf_t1_t3 h2 ρ
  have hL2 := le_add_inf_t1_u1_y1 h2 ρ
  have hf2 : f ≤ c2 + a := by
    have h := hL2.1
    rw [← hf, ← hc2, ← ha'] at h
    exact h.trans_eq (by rw [haa'])
  have hc2f : c2 ≤ f := by
    have h := hL2.2
    rw [← hf, ← hc2] at h
    exact h
  have hE9 : n + 3 * e = 2 * c1 + 2 * c2 := by
    have h := line_sum_t1 h3 ρ
    rw [← hn, ← he, ← hc1, ← hc2] at h
    exact h
  have hpar1 : Even (c1 - e) := by
    rw [hc1, he]
    exact even_sub_line_sum_t1 h2 h3 ρ
  have hpar2 : Even (c2 - e) := by
    have h := even_sub_line_sum_t1u1 (K := K) h2 h3 ρ
    rw [inf_ker_x3b9 ρ, finrank_ker_x3b9 ρ] at h
    rw [hc2, he]
    exact h
  have hec1 : e ≤ c1 := by
    rw [he, hc1]
    exact Submodule.finrank_mono inf_le_left
  obtain ⟨k, hk⟩ := hpar1
  obtain ⟨l, hl⟩ := hpar2
  exact three_le_of_dims hdim1 haf hm hf1 hc1f hf2 hc2f hE9 hec1 hk hl

theorem three_le_finrank_ker_sub_one_of_alternatingGroup_six {K : Type*} [Field K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (ρ : Representation K (alternatingGroup (Fin 6)) W) (hρ : ρ ≠ 1)
    {t : alternatingGroup (Fin 6)} (ht : t * t = 1) (ht1 : t ≠ 1) :
    3 ≤ Module.finrank K (LinearMap.ker (ρ t - 1)) := by
  obtain ⟨g, hg⟩ := exists_conj_eq_t1 ht ht1
  rw [← finrank_ker_sub_one_conj ρ g t, hg]
  exact three_le_finrank_ker_sub_one_t1 h2 h3 ρ hρ

end CFSG.RankThree.PartTwo.Sec16.Kcd166

end
