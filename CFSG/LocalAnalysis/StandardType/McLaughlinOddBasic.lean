module

public import CFSG.RankThree.PartOne.LIT.McSlA
public import CFSG.RankThree.PartOne.LIT.McPencil
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
public import CFSG.RankThree.PartOne.LIT.KF127Trans

public section

namespace CFSG.StandardType.McLaughlinOdd

open CFSG.RankThree.PartOne.LIT
open CFSG.RankThree.Classical (IsTransvectionWith isCompl_span_pair_ker_inf_ker)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

theorem exists_dual_one_of_notMem {W : Submodule (ZMod p) V} {x : V} (hx : x ∉ W) :
    ∃ f : Module.Dual (ZMod p) V, f x = 1 ∧ ∀ y ∈ W, f y = 0 := by
  obtain ⟨ψ, hψx, hψ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  refine ⟨(ψ x)⁻¹ • ψ, ?_, fun y hy => ?_⟩
  · rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hψx]
  · have h : ψ y ∈ W.map ψ := Submodule.mem_map_of_mem hy
    rw [hψ, Submodule.mem_bot] at h
    rw [LinearMap.smul_apply, h, smul_zero]

theorem notMem_sup_span_of_notMem_span {W L : Submodule (ZMod p) V} (hWL : Disjoint W L)
    {x y : V} (hx : x ∈ W) (hy : y ∈ W) (hxy : y ∉ Submodule.span (ZMod p) {x}) :
    y ∉ L ⊔ Submodule.span (ZMod p) {x} := by
  intro hmem
  obtain ⟨l, hl, z, hz, hlz⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have hlW : l ∈ W := by
    have : l = y - s • x := by rw [← hlz]; abel
    rw [this]
    exact W.sub_mem hy (W.smul_mem s hx)
  have hl0 : l = 0 := Submodule.disjoint_def.mp hWL l hlW hl
  rw [hl0, zero_add] at hlz
  exact hxy (Submodule.mem_span_singleton.mpr ⟨s, hlz⟩)

theorem finrank_span_pair_eq_two {v w : V} {f : Module.Dual (ZMod p) V} (hv : v ≠ 0)
    (hfv : f v = 0) (hfw : f w ≠ 0) :
    Module.finrank (ZMod p) (Submodule.span (ZMod p) {v, w}) = 2 := by
  have hli : LinearIndependent (ZMod p) ![v, w] := by
    refine LinearIndependent.pair_iff.mpr fun s t hst => ?_
    have hf := congrArg f hst
    rw [map_add, map_smul, map_smul, hfv, smul_eq_mul, smul_eq_mul, mul_zero, zero_add,
      map_zero] at hf
    have ht : t = 0 := (mul_eq_zero.mp hf).resolve_right hfw
    rw [ht, zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right hv, ht⟩
  have := finrank_span_eq_card hli
  rw [Fintype.card_fin] at this
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.union_singleton, Set.pair_comm] at this
  exact this

theorem eq_comb_of_vanish {a b : V} {φ g f : Module.Dual (ZMod p) V} (hφa : φ a = 0)
    (hgb : g b = 0) (hφb : φ b ≠ 0) (hga : g a ≠ 0)
    (hf : ∀ l ∈ LinearMap.ker φ ⊓ LinearMap.ker g, f l = 0) :
    f = (f b / φ b) • φ + (f a / g a) • g := by
  have hc := isCompl_span_pair_ker_inf_ker hφa hgb hφb hga
  refine LinearMap.ext_on_codisjoint hc.codisjoint (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hz
    simp only [map_add, map_smul, smul_eq_mul, LinearMap.add_apply, LinearMap.smul_apply, hφa,
      hgb]
    field_simp
    ring
  · have h1 : φ z = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hz).1
    have h2 : g z = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hz).2
    simp [h1, h2, hf z hz]

section Proj

variable {W L : Submodule (ZMod p) V} (hc : IsCompl W L)

@[expose] noncomputable def pW : V →ₗ[ZMod p] V := W.projection L hc

@[expose] noncomputable def pL : V →ₗ[ZMod p] V := L.projection W hc.symm

theorem pW_mem (x : V) : pW hc x ∈ W := Submodule.projection_apply_mem hc x

theorem pL_mem (x : V) : pL hc x ∈ L := Submodule.projection_apply_mem hc.symm x

theorem pW_add_pL (x : V) : pW hc x + pL hc x = x :=
  Submodule.projection_add_projection_eq_self hc x

theorem pW_of_mem {x : V} (hx : x ∈ W) : pW hc x = x :=
  Submodule.projection_apply_of_mem_left hc hx

theorem pW_of_mem_L {x : V} (hx : x ∈ L) : pW hc x = 0 :=
  Submodule.projection_apply_of_mem_right hc hx

theorem pL_of_mem {x : V} (hx : x ∈ L) : pL hc x = x :=
  Submodule.projection_apply_of_mem_left hc.symm hx

theorem pL_of_mem_W {x : V} (hx : x ∈ W) : pL hc x = 0 :=
  Submodule.projection_apply_of_mem_right hc.symm hx

theorem apply_eq_pW_add_pL (f : Module.Dual (ZMod p) V) (x : V) :
    f x = f (pW hc x) + f (pL hc x) := by
  rw [← map_add, pW_add_pL]

include hc in
theorem exists_mem_ne_zero_of_vanish {f : Module.Dual (ZMod p) V} (hfL : ∀ l ∈ L, f l = 0)
    (hf0 : f ≠ 0) : ∃ w ∈ W, f w ≠ 0 := by
  by_contra hno
  push Not at hno
  refine hf0 (LinearMap.ext fun x => ?_)
  rw [apply_eq_pW_add_pL hc, hno _ (pW_mem hc x), hfL _ (pL_mem hc x), add_zero,
    LinearMap.zero_apply]

end Proj

section TrInCalc

variable {H : Subgroup (V ≃ₗ[ZMod p] V)} {c c' : V} {f f' : Module.Dual (ZMod p) V}

theorem trIn_sub_center (h : TrIn H c f) (h' : TrIn H c' f) : TrIn H (c - c') f := by
  have hneg : TrIn H (-c') f := by
    have := TrIn.smul_center_iff.mpr (h'.smul (-1))
    rwa [neg_smul, one_smul] at this
  simpa [sub_eq_add_neg] using h.add_center hneg

theorem trIn_of_smul {s : ZMod p} (hs : s ≠ 0) (h : TrIn H c (s • f)) : TrIn H c f := by
  have := h.smul s⁻¹
  rwa [smul_smul, inv_mul_cancel₀ hs, one_smul] at this

theorem trIn_smul_both (h : TrIn H c f) (s : ZMod p) : TrIn H (s • c) (s • f) := by
  rw [TrIn.smul_center_iff, smul_smul]
  exact h.smul _

theorem symm_apply_of_trIn {t : V ≃ₗ[ZMod p] V} (hfc : f c = 0) (htx : ∀ x, t x = x + f x • c)
    (x : V) : t.symm x = x - f x • c :=
  TrIn.inv_apply hfc htx x

end TrInCalc

variable {H : Subgroup (V ≃ₗ[ZMod p] V)}

@[expose] def RelGood (H : Subgroup (V ≃ₗ[ZMod p] V)) (L : Submodule (ZMod p) V) (c : V) :
    Prop :=
  ∀ f : Module.Dual (ZMod p) V, (∀ l ∈ L, f l = 0) → f c = 0 → TrIn H c f

@[expose] def IsSLBlock (H : Subgroup (V ≃ₗ[ZMod p] V)) (W L : Submodule (ZMod p) V) : Prop :=
  IsCompl W L ∧ ∀ c ∈ W, RelGood H L c

theorem relGood_zero (L : Submodule (ZMod p) V) : RelGood H L 0 :=
  fun f _ _ => TrIn.zero_center f

namespace RelGood

variable {L : Submodule (ZMod p) V} {x y : V}

theorem smul (h : RelGood H L x) (s : ZMod p) : RelGood H L (s • x) := by
  intro f hfL hfc
  by_cases hs : s = 0
  · rw [hs, zero_smul]
    exact TrIn.zero_center f
  · have hfx : f x = 0 := by
      rw [map_smul, smul_eq_mul] at hfc
      exact (mul_eq_zero.mp hfc).resolve_left hs
    refine TrIn.smul_center_iff.mpr (h (s • f) (fun l hl => ?_) ?_)
    · rw [LinearMap.smul_apply, hfL l hl, smul_zero]
    · rw [LinearMap.smul_apply, hfx, smul_zero]

theorem add (hx : RelGood H L x) (hy : RelGood H L y)
    (hxy : y ∉ L ⊔ Submodule.span (ZMod p) {x}) : RelGood H L (x + y) := by
  obtain ⟨f₁, hf₁y, hf₁⟩ := exists_dual_one_of_notMem hxy
  have hf₁L : ∀ l ∈ L, f₁ l = 0 := fun l hl => hf₁ l (Submodule.mem_sup_left hl)
  have hf₁x : f₁ x = 0 :=
    hf₁ x (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))
  obtain ⟨-, t, ht, htx⟩ := hx f₁ hf₁L hf₁x
  intro f hfL hf
  have hty : t y = x + y := by rw [htx, hf₁y, one_smul, add_comm]
  have h1 : TrIn H y (f ∘ₗ t.toLinearMap) := by
    refine hy _ (fun l hl => ?_) ?_
    · change f (t l) = 0
      rw [htx, hf₁L l hl, zero_smul, add_zero, hfL l hl]
    · change f (t y) = 0
      rw [hty, hf]
  have h2 := h1.conj ht
  have hform : (f ∘ₗ t.toLinearMap) ∘ₗ t.symm.toLinearMap = f := by
    ext z
    simp
  rwa [hty, hform] at h2

end RelGood

theorem isSLBlock_of_span {W L : Submodule (ZMod p) V} (hc : IsCompl W L) {S : Set V}
    (hSW : Submodule.span (ZMod p) S = W) (hS : ∀ c ∈ S, RelGood H L c) : IsSLBlock H W L := by
  refine ⟨hc, ?_⟩
  let G : Submodule (ZMod p) V :=
    { carrier := {c | c ∈ W ∧ RelGood H L c}
      add_mem' := fun {x y} hx hy => by
        refine ⟨W.add_mem hx.1 hy.1, ?_⟩
        by_cases hyx : y ∈ Submodule.span (ZMod p) {x}
        · obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hyx
          have : x + s • x = (1 + s) • x := by module
          rw [this]
          exact hx.2.smul _
        · exact hx.2.add hy.2 (notMem_sup_span_of_notMem_span hc.disjoint hx.1 hy.1 hyx)
      zero_mem' := ⟨W.zero_mem, relGood_zero L⟩
      smul_mem' := fun s c hc' => ⟨W.smul_mem s hc'.1, hc'.2.smul s⟩ }
  have hle : W ≤ G := by
    rw [← hSW, Submodule.span_le]
    intro c hcS
    exact ⟨hSW ▸ Submodule.subset_span hcS, hS c hcS⟩
  intro c hcW
  exact (hle hcW).2

theorem isSLBlock_of_reciprocal {a b : V} {φ g : Module.Dual (ZMod p) V} (hφ : TrIn H a φ)
    (hg : TrIn H b g) (hφb : φ b ≠ 0) (hga : g a ≠ 0) :
    IsSLBlock H (Submodule.span (ZMod p) {a, b}) (LinearMap.ker φ ⊓ LinearMap.ker g) := by
  have hc := isCompl_span_pair_ker_inf_ker hφ.1 hg.1 hφb hga
  refine isSLBlock_of_span hc rfl ?_
  rintro c (rfl | hc')
  · intro f hfL hfc
    rw [eq_comb_of_vanish hφ.1 hg.1 hφb hga hfL, hfc, zero_div, zero_smul, add_zero]
    exact hφ.smul _
  · rw [Set.mem_singleton_iff] at hc'
    subst hc'
    intro f hfL hfc
    rw [eq_comb_of_vanish hφ.1 hg.1 hφb hga hfL, hfc, zero_div, zero_smul, zero_add]
    exact hg.smul _

end CFSG.StandardType.McLaughlinOdd
