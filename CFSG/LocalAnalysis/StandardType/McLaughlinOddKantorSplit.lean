module

public import CFSG.LocalAnalysis.StandardType.McLaughlinOddKantorBasic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

public section

namespace CFSG.StandardType.McLaughlinOdd

open CFSG.RankThree.PartOne.LIT
open CFSG.RankThree.Classical (IsTransvectionWith)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

theorem apply_eq_zero_of_mem_span_singleton {r w : V} {f : Module.Dual (ZMod p) V}
    (hf : f r = 0) (hw : w ∈ Submodule.span (ZMod p) {r}) : f w = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [map_smul, hf, smul_zero]

theorem exists_apply_eq_zero_apply_eq_one {φ f : Module.Dual (ZMod p) V}
    (h : f ∉ Submodule.span (ZMod p) {φ}) : ∃ u, φ u = 0 ∧ f u = 1 := by
  by_contra hno
  push Not at hno
  have hker : ∀ u, φ u = 0 → f u = 0 := by
    intro u hu
    by_contra hfu
    have := hno ((f u)⁻¹ • u) (by rw [map_smul, hu, smul_zero])
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hfu] at this
    exact this rfl
  apply h
  by_cases hφ : φ = 0
  · have hf : f = 0 := LinearMap.ext fun u => hker u (by rw [hφ, LinearMap.zero_apply])
    rw [hf]
    exact Submodule.zero_mem _
  · obtain ⟨x₀, hx₀⟩ : ∃ x, φ x ≠ 0 := by
      by_contra hno'
      push Not at hno'
      exact hφ (LinearMap.ext hno')
    refine Submodule.mem_span_singleton.mpr ⟨f x₀ / φ x₀, LinearMap.ext fun y => ?_⟩
    have h0 := hker (y - (φ y / φ x₀) • x₀) (by
      rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hx₀, sub_self])
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h0
    rw [LinearMap.smul_apply, smul_eq_mul, h0]
    field_simp

theorem exists_dual_vanish_three [Module.Finite (ZMod p) V] (hdim : 4 ≤ Module.finrank (ZMod p) V)
    (a b c : V) : ∃ f : Module.Dual (ZMod p) V, f ≠ 0 ∧ f a = 0 ∧ f b = 0 ∧ f c = 0 := by
  classical
  have hW : Module.finrank (ZMod p) (Submodule.span (ZMod p) ({a, b, c} : Set V)) ≤ 3 := by
    have := finrank_span_le_card (R := ZMod p) ({a, b, c} : Set V)
    have h3 : ({a, b, c} : Set V).toFinset.card ≤ 3 := by
      rw [Set.toFinset_insert, Set.toFinset_insert, Set.toFinset_singleton]
      exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
        (by simp)))
    omega
  set W := Submodule.span (ZMod p) ({a, b, c} : Set V) with hWdef
  obtain ⟨x, hx⟩ : ∃ x, x ∉ W := by
    by_contra hno
    push Not at hno
    have hWt : W = ⊤ := eq_top_iff.mpr fun x _ => hno x
    rw [hWt, finrank_top] at hW
    omega
  obtain ⟨f, hfx, hfW⟩ := exists_dual_one_of_notMem hx
  refine ⟨f, fun h0 => by rw [h0, LinearMap.zero_apply] at hfx; exact zero_ne_one hfx,
    hfW a (Submodule.subset_span (by simp)), hfW b (Submodule.subset_span (by simp)),
    hfW c (Submodule.subset_span (by simp))⟩

variable {T : Subgroup (V ≃ₗ[ZMod p] V)} {D : Set (V ≃ₗ[ZMod p] V)} {r : V}

structure SplitHyp (T : Subgroup (V ≃ₗ[ZMod p] V)) (D : Set (V ≃ₗ[ZMod p] V)) (r : V) : Prop where
  sub : D ⊆ T
  tr : ∀ t ∈ D, ∃ v f, IsTransvectionWith t v f
  span : cenSpan D = ⊤
  ne : r ≠ 0
  fix : ∀ g ∈ T, g r = r
  unip : ∀ g ∈ T, (∀ x, g x - x ∈ Submodule.span (ZMod p) {r}) → g = 1

namespace SplitHyp

variable (hS : SplitHyp T D r)
include hS

theorem fix_mem {g : V ≃ₗ[ZMod p] V} (hg : g ∈ T) {w : V} (hw : w ∈ Submodule.span (ZMod p) {r}) :
    g w = w := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [map_smul, hS.fix g hg]

theorem center_notMem {t : V ≃ₗ[ZMod p] V} (ht : t ∈ D) {v : V} {f : Module.Dual (ZMod p) V}
    (h : IsTransvectionWith t v f) : v ∉ Submodule.span (ZMod p) {r} ∧ f r = 0 := by
  refine ⟨fun hv => transvection_ne_one h (hS.unip t (hS.sub ht) fun x => ?_), ?_⟩
  · rw [h.2.2.2, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ hv
  · have := hS.fix t (hS.sub ht)
    rw [h.2.2.2] at this
    have h0 : f r • v = 0 := by simpa using this
    exact (smul_eq_zero.mp h0).resolve_right h.1

theorem eq_zero_of_trIn {w : V} {f : Module.Dual (ZMod p) V} (h : TrIn T w f)
    (hw : w ∈ Submodule.span (ZMod p) {r}) (hf : f ≠ 0) : w = 0 := by
  obtain ⟨-, τ, hτ, hτx⟩ := h
  have h1 := hS.unip τ hτ fun x => by
    rw [hτx, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ hw
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hf (LinearMap.ext hno)
  have h2 := hτx x
  rw [h1] at h2
  change x = x + f x • w at h2
  have h3 : f x • w = 0 := by
    have := congrArg (fun y => y - x) h2
    simpa using this.symm
  exact (smul_eq_zero.mp h3).resolve_left hx

theorem eq_of_trIn_sub_mem {v v' : V} {f : Module.Dual (ZMod p) V} (h : TrIn T v f)
    (h' : TrIn T v' f) (hf : f ≠ 0) (hvv' : v' - v ∈ Submodule.span (ZMod p) {r}) : v' = v :=
  sub_eq_zero.mp (hS.eq_zero_of_trIn (trIn_sub_center h' h) hvv' hf)

theorem exists_mem : ∃ t ∈ D, ∃ v f, IsTransvectionWith t v f := by
  by_contra hno
  push Not at hno
  have hD : cenSet D = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun v ⟨t, ht, f, h⟩ => ?_
    obtain ⟨v', f', h'⟩ := hS.tr t ht
    exact hno t ht v' f' h'
  have := hS.span
  rw [cenSpan, hD, Submodule.span_empty] at this
  exact hS.ne (by simpa [← this] using (Submodule.mem_top : r ∈ (⊤ : Submodule (ZMod p) V)))

theorem false_of_neg (hp : p ≠ 2) {z : V ≃ₗ[ZMod p] V} (hz : z ∈ T)
    (hzneg : ∀ x, z x + x ∈ Submodule.span (ZMod p) {r}) : False := by
  have hcen : ∀ g ∈ T, g * z = z * g := by
    intro g hg
    have hk : g * z * (z * g)⁻¹ ∈ T := T.mul_mem (T.mul_mem hg hz) (T.inv_mem (T.mul_mem hz hg))
    refine mul_inv_eq_one.mp (hS.unip _ hk fun x => ?_)
    obtain ⟨y, rfl⟩ : ∃ y, (z * g) y = x := ⟨(z * g).symm x, (z * g).apply_symm_apply _⟩
    rw [← LinearEquiv.mul_apply, inv_mul_cancel_right, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply]
    have e : g (z y) - z (g y) = g (z y + y) - (z (g y) + g y) := by rw [map_add]; abel
    rw [e, hS.fix_mem hg (hzneg y)]
    exact Submodule.sub_mem _ (hzneg y) (hzneg (g y))
  have hneg : ∀ v ∈ cenSet D, z v = -v := by
    rintro v ⟨t, ht, f, h⟩
    obtain ⟨x, hx⟩ : ∃ x, f x = 1 := by
      obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
        by_contra hno
        push Not at hno
        exact h.2.1 (LinearMap.ext hno)
      exact ⟨(f x)⁻¹ • x, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hx]⟩
    have e := LinearEquiv.congr_fun (hcen t (hS.sub ht)) x
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, h.2.2.2, h.2.2.2, map_add, map_smul, hx,
      one_smul] at e
    have hzv : z v = f (z x) • v := (add_left_cancel e).symm
    have hmem : (f (z x) + 1) • v ∈ Submodule.span (ZMod p) {r} := by
      rw [add_smul, one_smul, ← hzv]
      exact hzneg v
    by_cases hc : f (z x) + 1 = 0
    · rw [hzv, eq_neg_of_add_eq_zero_left hc, neg_smul, one_smul]
    · exfalso
      apply (hS.center_notMem ht h).1
      have := Submodule.smul_mem _ (f (z x) + 1)⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  have hall : ∀ y ∈ cenSpan D, z y = -y := by
    intro y hy
    refine Submodule.span_induction (p := fun y _ => z y = -y) (fun v hv => hneg v hv)
      (by simp) (fun a b _ _ ha hb => by rw [map_add, ha, hb, neg_add])
      (fun c a _ ha => by rw [map_smul, ha, smul_neg]) hy
  have hzr := hall r (hS.span ▸ Submodule.mem_top)
  rw [hS.fix z hz] at hzr
  have h2 : (2 : ZMod p) • r = 0 := by
    rw [two_smul]
    nth_rewrite 1 [hzr]
    exact neg_add_cancel r
  exact hS.ne ((smul_eq_zero.mp h2).resolve_left (two_ne_zero_of_ne_two hp))

end SplitHyp

theorem trIn_move {a : V} {φ : Module.Dual (ZMod p) V} (h : TrIn T a φ) (hφr : φ r = 0)
    {τ : V ≃ₗ[ZMod p] V} (hτ : τ ∈ T) {u : V} {g : Module.Dual (ZMod p) V}
    (hgu : g u = 0) (hτx : ∀ x, τ x - x - g x • u ∈ Submodule.span (ZMod p) {r})
    (hgr : g r = 0) : TrIn T (τ a) (φ - φ u • g) := by
  have hc := h.conj hτ
  have e : φ ∘ₗ τ.symm.toLinearMap = φ - φ u • g := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ : ∃ y, τ y = x := ⟨τ.symm x, τ.apply_symm_apply x⟩
    have hg : g (τ y - y - g y • u) = 0 := apply_eq_zero_of_mem_span_singleton hgr (hτx y)
    have hφ : φ (τ y - y - g y • u) = 0 := apply_eq_zero_of_mem_span_singleton hφr (hτx y)
    simp only [map_sub, map_smul, smul_eq_mul, hgu, mul_zero, sub_zero] at hg hφ
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    linear_combination -hφ + φ u * hg
  rwa [e] at hc

theorem notMem_span_singleton_comm {M : Type*} [AddCommGroup M] [Module (ZMod p) M] {x y : M}
    (hx : x ≠ 0) (h : y ∉ Submodule.span (ZMod p) {x}) : x ∉ Submodule.span (ZMod p) {y} := by
  intro hm
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hm
  have hs0 : s ≠ 0 := by rintro rfl; rw [zero_smul] at hs; exact hx hs.symm
  exact h (Submodule.mem_span_singleton.mpr ⟨s⁻¹, by rw [← hs, smul_smul, inv_mul_cancel₀ hs0,
    one_smul]⟩)

@[expose] def IsGood (T : Subgroup (V ≃ₗ[ZMod p] V)) (r x : V) : Prop :=
  ∀ f : Module.Dual (ZMod p) V, f r = 0 → f x = 0 → TrIn T x f

theorem isGood_smul {x : V} (hx : IsGood T r x) (c : ZMod p) : IsGood T r (c • x) := by
  intro f hfr hfx
  by_cases hc : c = 0
  · rw [hc, zero_smul]
    exact TrIn.zero_center f
  · have hfx' : f x = 0 := by
      rw [map_smul, smul_eq_mul] at hfx
      exact (mul_eq_zero.mp hfx).resolve_left hc
    exact TrIn.smul_center_iff.mpr (hx (c • f) (by rw [LinearMap.smul_apply, hfr, smul_zero])
      (by rw [LinearMap.smul_apply, hfx', smul_zero]))

namespace SplitHyp

variable (hS : SplitHyp T D r)
include hS

theorem exists_lift
    (hall : ∀ (u : V) (g : Module.Dual (ZMod p) V), g r = 0 → g u = 0 →
      ∃ τ ∈ T, ∀ x, τ x - x - g x • u ∈ Submodule.span (ZMod p) {r})
    {v : V} (hv : v ∉ Submodule.span (ZMod p) {r}) {f : Module.Dual (ZMod p) V} (hf0 : f ≠ 0)
    (hfr : f r = 0) (hfv : f v = 0) :
    ∃ v', v' - v ∈ Submodule.span (ZMod p) {r} ∧ TrIn T v' f := by
  obtain ⟨t₀, ht₀, v₀, f₀, h₀⟩ := hS.exists_mem
  have htr₀ : TrIn T v₀ f₀ := TrIn.of_isTransvectionWith (hS.sub ht₀) h₀
  obtain ⟨hv₀, hf₀r⟩ := hS.center_notMem ht₀ h₀
  obtain ⟨a₁, φ₁, ha₁, hφ₁0, hφ₁r, h₁⟩ : ∃ (a₁ : V) (φ₁ : Module.Dual (ZMod p) V),
      a₁ - v ∈ Submodule.span (ZMod p) {r} ∧ φ₁ ≠ 0 ∧ φ₁ r = 0 ∧ TrIn T a₁ φ₁ := by
    by_cases hvv₀ : v ∈ Submodule.span (ZMod p) {r} ⊔ Submodule.span (ZMod p) {v₀}
    · obtain ⟨ρ, hρ, w, hw, hρw⟩ := Submodule.mem_sup.mp hvv₀
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      have hc : c ≠ 0 := by
        rintro rfl
        rw [zero_smul, add_zero] at hρw
        exact hv (hρw ▸ hρ)
      refine ⟨c • v₀, c⁻¹ • f₀, ?_, smul_ne_zero (inv_ne_zero hc) h₀.2.1,
        by rw [LinearMap.smul_apply, hf₀r, smul_zero], ?_⟩
      · have : c • v₀ - v = -ρ := by rw [← hρw]; abel
        rw [this]
        exact Submodule.neg_mem _ hρ
      · rw [TrIn.smul_center_iff, smul_smul, mul_inv_cancel₀ hc, one_smul]
        exact htr₀
    · obtain ⟨g₁, hg₁v, hg₁⟩ := exists_dual_one_of_notMem hvv₀
      obtain ⟨g₂, hg₂v₀, hg₂⟩ := exists_dual_one_of_notMem hv₀
      have hg₁r : g₁ r = 0 :=
        hg₁ r (Submodule.mem_sup_left (Submodule.mem_span_singleton_self r))
      have hg₁v₀ : g₁ v₀ = 0 :=
        hg₁ v₀ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v₀))
      have hg₂r : g₂ r = 0 := hg₂ r (Submodule.mem_span_singleton_self r)
      set g := g₂ + (1 - g₂ v) • g₁ with hgdef
      have hgr : g r = 0 := by simp [hgdef, hg₁r, hg₂r]
      have hgv₀ : g v₀ = 1 := by simp [hgdef, hg₁v₀, hg₂v₀]
      have hgv : g v = 1 := by simp [hgdef, hg₁v]
      have hgu : g (v - v₀) = 0 := by rw [map_sub, hgv, hgv₀, sub_self]
      obtain ⟨τ, hτ, hτx⟩ := hall (v - v₀) g hgr hgu
      refine ⟨τ v₀, f₀ - f₀ (v - v₀) • g, ?_, ?_, by simp [hf₀r, hgr],
        trIn_move htr₀ hf₀r hτ hgu hτx hgr⟩
      · have := hτx v₀
        rw [hgv₀, one_smul] at this
        convert this using 1
        abel
      · intro h0
        have h1 := LinearMap.congr_fun h0 v₀
        rw [LinearMap.sub_apply, LinearMap.smul_apply, h₀.2.2.1, hgv₀, smul_eq_mul, mul_one,
          zero_sub, LinearMap.zero_apply, neg_eq_zero] at h1
        rw [h1, zero_smul, sub_zero] at h0
        exact h₀.2.1 h0
  by_cases hfφ : f ∈ Submodule.span (ZMod p) {φ₁}
  · obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hfφ
    exact ⟨a₁, ha₁, h₁.smul s⟩
  · have hφf := notMem_span_singleton_comm hφ₁0 hfφ
    obtain ⟨u₁, hu₁φ, hu₁f⟩ := exists_apply_eq_zero_apply_eq_one hfφ
    obtain ⟨u₂, hu₂f, hu₂φ⟩ := exists_apply_eq_zero_apply_eq_one hφf
    have hφu : φ₁ (u₁ + u₂) = 1 := by rw [map_add, hu₁φ, hu₂φ, zero_add]
    have hfu : f (u₁ + u₂) = 1 := by rw [map_add, hu₁f, hu₂f, add_zero]
    have hgr : (φ₁ - f) r = 0 := by rw [LinearMap.sub_apply, hφ₁r, hfr, sub_zero]
    have hgu : (φ₁ - f) (u₁ + u₂) = 0 := by rw [LinearMap.sub_apply, hφu, hfu, sub_self]
    obtain ⟨τ, hτ, hτx⟩ := hall (u₁ + u₂) (φ₁ - f) hgr hgu
    have hmove := trIn_move h₁ hφ₁r hτ hgu hτx hgr
    rw [hφu, one_smul, sub_sub_cancel] at hmove
    refine ⟨τ a₁, ?_, hmove⟩
    have hfa₁ : f a₁ = 0 := by
      have := apply_eq_zero_of_mem_span_singleton hfr ha₁
      rwa [map_sub, hfv, sub_zero] at this
    have hga₁ : (φ₁ - f) a₁ = 0 := by rw [LinearMap.sub_apply, h₁.1, hfa₁, sub_zero]
    have h2 := hτx a₁
    rw [hga₁, zero_smul, sub_zero] at h2
    have h3 := Submodule.add_mem _ h2 ha₁
    rwa [sub_add_sub_cancel] at h3

theorem exists_good [Module.Finite (ZMod p) V] (hdim : 4 ≤ Module.finrank (ZMod p) V)
    (hall : ∀ (u : V) (g : Module.Dual (ZMod p) V), g r = 0 → g u = 0 →
      ∃ τ ∈ T, ∀ x, τ x - x - g x • u ∈ Submodule.span (ZMod p) {r})
    {v : V} (hv : v ∉ Submodule.span (ZMod p) {r}) :
    ∃ v', v' - v ∈ Submodule.span (ZMod p) {r} ∧ IsGood T r v' := by
  obtain ⟨f₁, hf₁0, hf₁r, hf₁v, -⟩ := exists_dual_vanish_three hdim r v v
  obtain ⟨v', hv'v, h'⟩ := hS.exists_lift hall hv hf₁0 hf₁r hf₁v
  refine ⟨v', hv'v, fun f hfr hfv' => ?_⟩
  by_cases hf0 : f = 0
  · rw [hf0]
    exact TrIn.zero_axis v'
  by_cases hff₁ : f ∈ Submodule.span (ZMod p) {f₁}
  · obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hff₁
    exact h'.smul s
  have hf₁f := notMem_span_singleton_comm hf₁0 hff₁
  obtain ⟨w, hfw, hf₁w⟩ := exists_apply_eq_zero_apply_eq_one hf₁f
  have hw : w ∉ Submodule.span (ZMod p) {r} := fun hwR => by
    rw [apply_eq_zero_of_mem_span_singleton hf₁r hwR] at hf₁w
    exact zero_ne_one hf₁w
  obtain ⟨w', hw'w, hw'⟩ := hS.exists_lift hall hw hf0 hfr hfw
  have hR := TrIn.rule_R h' hw' hfv'
  have h1 : f₁ w' = 1 := by
    have := apply_eq_zero_of_mem_span_singleton hf₁r hw'w
    rw [map_sub, hf₁w, sub_eq_zero] at this
    exact this
  rwa [h1, one_smul] at hR

theorem isGood_add [Module.Finite (ZMod p) V] (hdim : 4 ≤ Module.finrank (ZMod p) V)
    (hall : ∀ (u : V) (g : Module.Dual (ZMod p) V), g r = 0 → g u = 0 →
      ∃ τ ∈ T, ∀ x, τ x - x - g x • u ∈ Submodule.span (ZMod p) {r})
    {x y : V} (hx : IsGood T r x) (hy : IsGood T r y) : IsGood T r (x + y) := by
  obtain ⟨f', hf'0, hf'r, hf'x, hf'y⟩ := exists_dual_vanish_three hdim r x y
  have h₁ : TrIn T (x + y) f' := (hx f' hf'r hf'x).add_center (hy f' hf'r hf'y)
  by_cases hxy : x + y ∈ Submodule.span (ZMod p) {r}
  · rw [hS.eq_zero_of_trIn h₁ hxy hf'0]
    exact fun f _ _ => TrIn.zero_center f
  · obtain ⟨s, hs, hgs⟩ := hS.exists_good hdim hall hxy
    have hf's : f' s = 0 := by
      have := apply_eq_zero_of_mem_span_singleton hf'r hs
      rw [map_sub, sub_eq_zero] at this
      rw [this, map_add, hf'x, hf'y, add_zero]
    rw [← hS.eq_of_trIn_sub_mem h₁ (hgs f' hf'r hf's) hf'0 hs]
    exact hgs

theorem isGood_center [Module.Finite (ZMod p) V] (hdim : 4 ≤ Module.finrank (ZMod p) V)
    (hall : ∀ (u : V) (g : Module.Dual (ZMod p) V), g r = 0 → g u = 0 →
      ∃ τ ∈ T, ∀ x, τ x - x - g x • u ∈ Submodule.span (ZMod p) {r})
    {t : V ≃ₗ[ZMod p] V} (ht : t ∈ D) {v : V} {f : Module.Dual (ZMod p) V}
    (h : IsTransvectionWith t v f) : IsGood T r v := by
  obtain ⟨hv, hfr⟩ := hS.center_notMem ht h
  obtain ⟨v', hv'v, hg⟩ := hS.exists_good hdim hall hv
  have hfv' : f v' = 0 := by
    have := apply_eq_zero_of_mem_span_singleton hfr hv'v
    rwa [map_sub, h.2.2.1, sub_zero] at this
  rw [← hS.eq_of_trIn_sub_mem (TrIn.of_isTransvectionWith (hS.sub ht) h) (hg f hfr hfv') h.2.1
    hv'v]
  exact hg

theorem false_of_lift [Module.Finite (ZMod p) V] (hdim : 4 ≤ Module.finrank (ZMod p) V)
    (hall : ∀ (u : V) (g : Module.Dual (ZMod p) V), g r = 0 → g u = 0 →
      ∃ τ ∈ T, ∀ x, τ x - x - g x • u ∈ Submodule.span (ZMod p) {r}) : False := by
  have hgood : ∀ y ∈ cenSpan D, IsGood T r y := by
    intro y hy
    refine Submodule.span_induction (p := fun y _ => IsGood T r y)
      (fun v hv => by obtain ⟨t, ht, f, h⟩ := hv; exact hS.isGood_center hdim hall ht h)
      (fun f _ _ => TrIn.zero_center f) (fun a b _ _ ha hb => hS.isGood_add hdim hall ha hb)
      (fun c a _ ha => isGood_smul ha c) hy
  have hr := hgood r (hS.span ▸ Submodule.mem_top)
  obtain ⟨f', hf'0, hf'r, -, -⟩ := exists_dual_vanish_three hdim r r r
  exact hS.ne (hS.eq_zero_of_trIn (hr f' hf'r hf'r) (Submodule.mem_span_singleton_self r) hf'0)

end SplitHyp

end CFSG.StandardType.McLaughlinOdd
