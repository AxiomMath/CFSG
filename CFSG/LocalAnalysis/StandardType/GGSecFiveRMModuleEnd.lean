module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

public section

namespace CFSG.StandardType

section Module

private lemma ggLinMove_smul_involution
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (r : V ≃ₗ[ZMod p] V) (hr : r * r = 1) :
    ∀ x ∈ ggLinMove r, r x = -x := by
  rintro x ⟨v, rfl⟩
  have hr' : r.toLinearMap (r.toLinearMap v) = v := by
    have h := congrArg (fun e : V ≃ₗ[ZMod p] V => e v) hr
    simpa [LinearEquiv.mul_apply] using h
  change r.toLinearMap ((r.toLinearMap - LinearMap.id : V →ₗ[ZMod p] V) v) =
    -((r.toLinearMap - LinearMap.id : V →ₗ[ZMod p] V) v)
  rw [LinearMap.sub_apply, LinearMap.id_apply, map_sub, hr']
  abel

private lemma ggLinCom_map_le
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (A : Subgroup (V ≃ₗ[ZMod p] V)) {g : V ≃ₗ[ZMod p] V} (hg : g ∈ A) :
    (ggLinCom (A : Set (V ≃ₗ[ZMod p] V))).map g.toLinearMap ≤
      ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) := by
  rw [ggLinCom, Submodule.map_iSup]
  refine iSup_le fun a => ?_
  rw [Submodule.map_iSup]
  refine iSup_le fun ha => ?_
  intro x hx
  rcases (Submodule.mem_map.mp hx) with ⟨v, hv, rfl⟩
  rcases hv with ⟨w, rfl⟩
  have hmem : g * a * g⁻¹ ∈ A := A.mul_mem (A.mul_mem hg ha) (A.inv_mem hg)
  have heq : g.toLinearMap ((a.toLinearMap - LinearMap.id : V →ₗ[ZMod p] V) w) =
      ((g * a * g⁻¹).toLinearMap - LinearMap.id : V →ₗ[ZMod p] V) (g.toLinearMap w) := by
    simp [LinearMap.sub_apply]
  change g.toLinearMap ((a.toLinearMap - LinearMap.id : V →ₗ[ZMod p] V) w) ∈
    ggLinCom (A : Set (V ≃ₗ[ZMod p] V))
  rw [heq]
  exact Submodule.mem_iSup_of_mem (g * a * g⁻¹)
    (Submodule.mem_iSup_of_mem hmem ⟨g w, rfl⟩)

theorem ggLin_end_scalar
    {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (hp2 : p ≠ 2) (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hprop : ∀ W : Submodule (ZMod p) V, (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) →
      W ≤ ggLinFix (A : Set (V ≃ₗ[ZMod p] V)) ∨ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) ≤ W)
    (hfix : ggLinFix (A : Set (V ≃ₗ[ZMod p] V)) = ⊥)
    (s : V ≃ₗ[ZMod p] V) (hs : s ∈ A) (hsr : GGLinRefl s) :
    ∀ f : V →ₗ[ZMod p] V, LinearMap.range f ≤ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)) →
      (∀ a ∈ A, ∀ u ∈ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)), f (a u) = a (f u)) →
      ∃ c : ZMod p, ∀ u ∈ ggLinCom (A : Set (V ≃ₗ[ZMod p] V)), f u = c • u := by
  intro f _hfrange hfcomm
  let U : Submodule (ZMod p) V := ggLinCom (A : Set (V ≃ₗ[ZMod p] V))
  have hUstable : ∀ a ∈ A, ∀ u ∈ U, a u ∈ U := by
    intro a ha u hu
    have hmap := ggLinCom_map_le (A := A) (g := a) ha
    exact hmap (Submodule.mem_map.mpr ⟨u, hu, rfl⟩)
  have hsm : ∀ x ∈ ggLinMove s, s x = -x := ggLinMove_smul_involution s hsr.1
  have hnt : Nontrivial (ggLinMove s) :=
    Module.nontrivial_of_finrank_eq_succ (R := ZMod p) (M := ggLinMove s) (n := 0) hsr.2
  obtain ⟨e, he0⟩ := exists_ne (0 : ggLinMove s)
  have he_mem : (e : V) ∈ ggLinMove s := e.2
  have he_ne : (e : V) ≠ 0 := by
    intro h
    exact he0 (Subtype.ext (by simpa using h))
  have heU : (e : V) ∈ U :=
    Submodule.mem_iSup_of_mem s (Submodule.mem_iSup_of_mem hs he_mem)
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using hzero)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p) Nat.prime_two).mp hdvd)
  let t : ZMod p := -(2 : ZMod p)
  have ht : t ≠ 0 := by
    dsimp [t]
    exact neg_ne_zero.mpr h2
  have hse : s (e : V) = -(e : V) := hsm (e : V) he_mem
  have hsfe : s (f (e : V)) = -(f (e : V)) := by
    rw [← hfcomm s hs (e : V) heU, hse, map_neg]
  have hminus : ((s : V →ₗ[ZMod p] V) - LinearMap.id : V →ₗ[ZMod p] V) (f (e : V)) =
      t • f (e : V) := by
    dsimp [t]
    rw [hsfe]
    show -(f (e : V)) - f (e : V) = (-2 : ZMod p) • f (e : V)
    rw [neg_smul, two_smul]
    abel
  have hfe_range : f (e : V) ∈ ggLinMove s := by
    refine ⟨t⁻¹ • f (e : V), ?_⟩
    show ((s : V →ₗ[ZMod p] V) - LinearMap.id : V →ₗ[ZMod p] V) (t⁻¹ • f (e : V)) = f (e : V)
    rw [map_smul, hminus, smul_smul, inv_mul_cancel₀ ht, one_smul]
  obtain ⟨c, hc⟩ : ∃ c : ZMod p, c • (e : V) = f (e : V) := by
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one (K := ZMod p) (V := ggLinMove s)
      hsr.2 he0 ⟨f (e : V), hfe_range⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  let W : Submodule (ZMod p) V :=
    LinearMap.ker (f - c • LinearMap.id : V →ₗ[ZMod p] V) ⊓ U
  have heW : (e : V) ∈ W := by
    refine ⟨?_, heU⟩
    change (f - c • LinearMap.id : V →ₗ[ZMod p] V) (e : V) = 0
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, ← hc]
    abel
  have hWstab : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W := by
    intro a ha w hw
    have hwU : w ∈ U := hw.2
    have hw1 : f w = c • w := by
      have h1 : (f - c • LinearMap.id : V →ₗ[ZMod p] V) w = 0 := hw.1
      rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at h1
      exact sub_eq_zero.mp h1
    refine ⟨?_, hUstable a ha w hwU⟩
    change (f - c • LinearMap.id : V →ₗ[ZMod p] V) (a w) = 0
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      hfcomm a ha w hwU, hw1, map_smul]
    simp
  have hWnot : ¬ W ≤ ggLinFix (A : Set (V ≃ₗ[ZMod p] V)) := by
    intro hle
    have hefix : (e : V) ∈ ggLinFix (A : Set (V ≃ₗ[ZMod p] V)) := hle heW
    rw [hfix] at hefix
    exact he_ne (by simpa using hefix)
  have hUW : U ≤ W := by
    rcases hprop W hWstab with h | h
    · exact absurd h hWnot
    · exact h
  refine ⟨c, fun u hu => ?_⟩
  have h1 : (f - c • LinearMap.id : V →ₗ[ZMod p] V) u = 0 := (hUW hu).1
  rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at h1
  exact sub_eq_zero.mp h1

end Module

end CFSG.StandardType

end
