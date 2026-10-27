module

public import CFSG.LocalAnalysis.StandardType.McLaughlinOddBasic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

public section

namespace CFSG.StandardType.McLaughlinOdd

open CFSG.RankThree.PartOne.LIT
open CFSG.RankThree.Classical (IsTransvectionWith invariant_of_generators)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
  {H : Subgroup (V ≃ₗ[ZMod p] V)}

namespace IsSLBlock

variable {W L : Submodule (ZMod p) V} (hB : IsSLBlock H W L)
include hB

theorem trIn_center_of_vanish {lam : Module.Dual (ZMod p) V} (hlam : ∀ y ∈ W, lam y = 0)
    {w : V} (hw : w ∈ W) (hw0 : w ≠ 0) (h : TrIn H w lam) : ∀ w' ∈ W, TrIn H w' lam := by
  intro w' hw'
  by_cases hspan : w' ∈ Submodule.span (ZMod p) {w}
  · obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hspan
    exact TrIn.smul_center_iff.mpr (h.smul s)
  have hnot : w ∉ L ⊔ Submodule.span (ZMod p) {w'} := by
    refine notMem_sup_span_of_notMem_span hB.1.disjoint hw' hw fun hmem => hspan ?_
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hmem
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hs
      exact hw0 hs.symm
    exact Submodule.mem_span_singleton.mpr ⟨s⁻¹, by rw [← hs, smul_smul, inv_mul_cancel₀ hs0,
      one_smul]⟩
  obtain ⟨φ, hφw, hφ⟩ := exists_dual_one_of_notMem hnot
  have hφL : ∀ l ∈ L, φ l = 0 := fun l hl => hφ l (Submodule.mem_sup_left hl)
  have hφw' : φ w' = 0 :=
    hφ w' (Submodule.mem_sup_right (Submodule.mem_span_singleton_self w'))
  obtain ⟨-, t, ht, htx⟩ := hB.2 w' hw' φ hφL hφw'
  have htw : t w = w + w' := by rw [htx, hφw, one_smul]
  have hform : lam ∘ₗ t.symm.toLinearMap = lam := by
    ext z
    change lam (t.symm z) = lam z
    rw [symm_apply_of_trIn hφw' htx z, map_sub, map_smul, hlam w' hw', smul_zero, sub_zero]
  have h1 := h.conj ht
  rw [htw, hform] at h1
  have := trIn_sub_center h1 h
  rwa [add_sub_cancel_left] at this

theorem trIn_axis_of_vanish {l : V} (hl : l ∈ L) {f : Module.Dual (ZMod p) V}
    (hfL : ∀ y ∈ L, f y = 0) (hf0 : f ≠ 0) (h : TrIn H l f) :
    ∀ φ : Module.Dual (ZMod p) V, (∀ y ∈ L, φ y = 0) → TrIn H l φ := by
  obtain ⟨c, hcW, hfc⟩ := exists_mem_ne_zero_of_vanish hB.1 hfL hf0
  intro φ hφL
  obtain ⟨f', hf'⟩ : ∃ f' : Module.Dual (ZMod p) V, f' = φ - (φ c / f c) • f := ⟨_, rfl⟩
  have hf'L : ∀ y ∈ L, f' y = 0 := fun y hy => by
    rw [hf', LinearMap.sub_apply, LinearMap.smul_apply, hφL y hy, hfL y hy, smul_zero, sub_zero]
  have hf'c : f' c = 0 := by
    rw [hf', LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hfc,
      sub_self]
  obtain ⟨-, t, ht, htx⟩ := hB.2 c hcW f' hf'L hf'c
  have htl : t l = l := by rw [htx, hf'L l hl, zero_smul, add_zero]
  have hform : f ∘ₗ t.symm.toLinearMap = f - f c • f' := by
    ext z
    change f (t.symm z) = _
    rw [symm_apply_of_trIn hf'c htx z, map_sub, map_smul, smul_eq_mul, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, mul_comm]
  have h1 := h.conj ht
  rw [htl, hform] at h1
  have h2 : TrIn H l (f c • f') := by
    have := h.sub h1
    rwa [sub_sub_cancel] at this
  have h3 := (trIn_of_smul hfc h2).add (h.smul (φ c / f c))
  rwa [hf', sub_add_cancel] at h3

theorem isAplus_comp_pL {w : V} (hw : w ∈ W) (hw0 : w ≠ 0) {χ : Module.Dual (ZMod p) V}
    (h : TrIn H w χ) : IsAplus H W (χ ∘ₗ pL hB.1) := by
  have hvanW : ∀ y ∈ W, (χ ∘ₗ pL hB.1) y = 0 := fun y hy => by
    rw [LinearMap.comp_apply, pL_of_mem_W hB.1 hy, map_zero]
  refine ⟨hvanW, ?_⟩
  have hW : TrIn H w (χ ∘ₗ pW hB.1) := by
    refine hB.2 w hw _ (fun l hl => ?_) ?_
    · rw [LinearMap.comp_apply, pW_of_mem_L hB.1 hl, map_zero]
    · rw [LinearMap.comp_apply, pW_of_mem hB.1 hw]
      exact h.1
  have hsub : χ ∘ₗ pL hB.1 = χ - χ ∘ₗ pW hB.1 := LinearMap.ext fun z => by
    rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      apply_eq_pW_add_pL hB.1 χ z]
    abel
  exact hB.trIn_center_of_vanish hvanW hw hw0 (by rw [hsub]; exact h.sub hW)

theorem isAminus_pL {f : Module.Dual (ZMod p) V} (hfL : ∀ y ∈ L, f y = 0) (hf0 : f ≠ 0)
    {y : V} (h : TrIn H y f) : IsAminus H L (pL hB.1 y) := by
  have hfy : f (pW hB.1 y) = 0 := by
    have := apply_eq_pW_add_pL hB.1 f y
    rw [h.1, hfL _ (pL_mem hB.1 y), add_zero] at this
    exact this.symm
  have hW : TrIn H (pW hB.1 y) f := hB.2 _ (pW_mem hB.1 y) f hfL hfy
  have hL : TrIn H (pL hB.1 y) f := by
    have := trIn_sub_center h hW
    rwa [(eq_sub_of_add_eq' (pW_add_pL hB.1 y)).symm] at this
  exact ⟨pL_mem hB.1 y, hB.trIn_axis_of_vanish (pL_mem hB.1 y) hfL hf0 hL⟩

end IsSLBlock

private theorem apply_of_vanish_inf_ker {L : Submodule (ZMod p) V} {ψ f : Module.Dual (ZMod p) V}
    {l : V} (hl : l ∈ L) (hψl : ψ l ≠ 0) (hf : ∀ y ∈ L ⊓ LinearMap.ker ψ, f y = 0) {y : V}
    (hy : y ∈ L) : f y = ψ y / ψ l * f l := by
  have hmem : y - (ψ y / ψ l) • l ∈ L ⊓ LinearMap.ker ψ := by
    refine Submodule.mem_inf.mpr ⟨L.sub_mem hy (L.smul_mem _ hl), ?_⟩
    rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hψl, sub_self]
  have := hf _ hmem
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at this
  exact this

namespace IsSLBlock

variable {W L : Submodule (ZMod p) V} (hB : IsSLBlock H W L)
include hB

theorem ystep {ψ : Module.Dual (ZMod p) V} (hψ : IsAplus H W ψ) {l : V} (hl : IsAminus H L l)
    (hψl : ψ l ≠ 0) :
    IsSLBlock H (W ⊔ Submodule.span (ZMod p) {l}) (L ⊓ LinearMap.ker ψ) := by
  have hc : IsCompl (W ⊔ Submodule.span (ZMod p) {l}) (L ⊓ LinearMap.ker ψ) := by
    refine ⟨Submodule.disjoint_def.mpr fun z hz1 hz2 => ?_, codisjoint_iff.mpr ?_⟩
    · obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.mp hz1
      obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hy
      obtain ⟨hzL, hzψ⟩ := Submodule.mem_inf.mp hz2
      rw [LinearMap.mem_ker, map_add, map_smul, hψ.1 w hw, zero_add, smul_eq_mul] at hzψ
      have hs : s = 0 := (mul_eq_zero.mp hzψ).resolve_right hψl
      rw [hs, zero_smul, add_zero] at hzL ⊢
      exact Submodule.disjoint_def.mp hB.1.disjoint w hw hzL
    · refine eq_top_iff.mpr fun z _ => ?_
      rw [← pW_add_pL hB.1 z]
      have hsplit : pL hB.1 z = (ψ (pL hB.1 z) / ψ l) • l +
          (pL hB.1 z - (ψ (pL hB.1 z) / ψ l) • l) := by abel
      rw [hsplit, ← add_assoc]
      refine Submodule.add_mem_sup (Submodule.add_mem_sup (pW_mem hB.1 z)
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self l))) ?_
      refine Submodule.mem_inf.mpr ⟨L.sub_mem (pL_mem hB.1 z) (L.smul_mem _ hl.1), ?_⟩
      rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hψl, sub_self]
  refine isSLBlock_of_span hc (S := (W : Set V) ∪ {l}) ?_ ?_
  · rw [Submodule.span_union, Submodule.span_eq]
  rintro c (hcW | hcl)
  · intro f hfL hfc
    have hfψ : ∀ y ∈ L, (f - (f l / ψ l) • ψ) y = 0 := fun y hy => by
      rw [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        apply_of_vanish_inf_ker hl.1 hψl hfL hy]
      field_simp
      ring
    have h1 : TrIn H c (f - (f l / ψ l) • ψ) := by
      refine hB.2 c hcW _ hfψ ?_
      rw [LinearMap.sub_apply, LinearMap.smul_apply, hfc, hψ.1 c hcW, smul_zero, sub_zero]
    have := h1.add ((hψ.2 c hcW).smul (f l / ψ l))
    rwa [sub_add_cancel] at this
  · rw [Set.mem_singleton_iff] at hcl
    subst hcl
    intro f hfL hfc
    refine hl.2 f fun y hy => ?_
    rw [apply_of_vanish_inf_ker hl.1 hψl hfL hy, hfc, mul_zero]

end IsSLBlock

@[expose] def aminusSub (H : Subgroup (V ≃ₗ[ZMod p] V)) (L : Submodule (ZMod p) V) :
    Submodule (ZMod p) V where
  carrier := {l | IsAminus H L l}
  add_mem' := fun hx hy =>
    ⟨L.add_mem hx.1 hy.1, fun φ hφ => (hx.2 φ hφ).add_center (hy.2 φ hφ)⟩
  zero_mem' := ⟨L.zero_mem, fun φ _ => TrIn.zero_center φ⟩
  smul_mem' := fun s _ hx =>
    ⟨L.smul_mem s hx.1, fun φ hφ => TrIn.smul_center_iff.mpr ((hx.2 φ hφ).smul s)⟩

theorem mem_aminusSub {L : Submodule (ZMod p) V} {l : V} : l ∈ aminusSub H L ↔ IsAminus H L l :=
  Iff.rfl

theorem exists_generator_moving {S : Set (V ≃ₗ[ZMod p] V)}
    (hirr : ∀ X : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ X, h x ∈ X) → X = ⊥ ∨ X = ⊤)
    (hS : ∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) (hHS : H = Subgroup.closure S)
    {X : Submodule (ZMod p) V} (hX0 : X ≠ ⊥) (hXt : X ≠ ⊤) :
    ∃ t ∈ S, ∃ (y : V) (e : Module.Dual (ZMod p) V), IsTransvectionWith t y e ∧
      y ∉ X ∧ ∃ z ∈ X, e z ≠ 0 := by
  by_contra hno
  push Not at hno
  have hinv : ∀ t ∈ S, ∀ x ∈ X, t x ∈ X ∧ t⁻¹ x ∈ X := by
    intro t ht x hx
    obtain ⟨y, e, hte⟩ := hS t ht
    by_cases hy : y ∈ X
    · rw [hte.2.2.2 x, hte.inv_apply x]
      exact ⟨X.add_mem hx (X.smul_mem _ hy), X.sub_mem hx (X.smul_mem _ hy)⟩
    · have hex := hno t ht y e hte hy x hx
      rw [hte.2.2.2 x, hte.inv_apply x, hex, zero_smul, add_zero, sub_zero]
      exact ⟨hx, hx⟩
  rcases hirr X (invariant_of_generators hHS hinv) with h | h
  · exact hX0 h
  · exact hXt h


namespace IsSLBlock

variable {W L : Submodule (ZMod p) V} (hB : IsSLBlock H W L)
include hB

theorem exists_of_aplus
    (hirr : ∀ X : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ X, h x ∈ X) → X = ⊥ ∨ X = ⊤)
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S)
    (hW2 : ∀ e : Module.Dual (ZMod p) V, ∃ w ∈ W, w ≠ 0 ∧ e w = 0)
    {ψ₀ : Module.Dual (ZMod p) V} (hψ₀ : IsAplus H W ψ₀) (hψ₀0 : ψ₀ ≠ 0) :
    ∃ ψ l, IsAplus H W ψ ∧ IsAminus H L l ∧ ψ l ≠ 0 := by
  obtain ⟨S, hS, hHS⟩ := hgen
  let K : Submodule (ZMod p) V :=
    { carrier := {v | ∀ ψ, IsAplus H W ψ → ψ v = 0}
      add_mem' := fun hx hy ψ hψ => by rw [map_add, hx ψ hψ, hy ψ hψ, add_zero]
      zero_mem' := fun ψ _ => map_zero ψ
      smul_mem' := fun s _ hx ψ hψ => by rw [map_smul, hx ψ hψ, smul_zero] }
  have hWK : W ≤ K := fun w hw ψ hψ => hψ.1 w hw
  have hK0 : K ≠ ⊥ := by
    intro hK
    obtain ⟨w, hw, hw0, -⟩ := hW2 0
    have hwK : w ∈ K := hWK hw
    rw [hK] at hwK
    exact hw0 ((Submodule.mem_bot (ZMod p)).mp hwK)
  have hKt : K ≠ ⊤ := by
    intro hK
    refine hψ₀0 (LinearMap.ext fun v => ?_)
    have hv : v ∈ K := hK ▸ Submodule.mem_top
    exact hv ψ₀ hψ₀
  obtain ⟨t, htS, y, e, hte, hyK, z, hzK, hez⟩ := exists_generator_moving hirr hS hHS hK0 hKt
  have hTr : TrIn H y e := TrIn.of_isTransvectionWith (hHS ▸ Subgroup.subset_closure htS) hte
  obtain ⟨ψ, hψ, hψy⟩ : ∃ ψ, IsAplus H W ψ ∧ ψ y ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hyK hno
  obtain ⟨w₁, hw₁, hw₁0, hew₁⟩ := hW2 e
  have h1 : TrIn H w₁ e := trIn_of_smul hψy (TrIn.rule_R (hψ.2 w₁ hw₁) hTr hew₁)
  have hP := hB.isAplus_comp_pL hw₁ hw₁0 h1
  have hezW : e (pW hB.1 z) ≠ 0 := by
    have h2 := apply_eq_pW_add_pL hB.1 e z
    have hPz : e (pL hB.1 z) = 0 := hzK _ hP
    rw [hPz, add_zero] at h2
    rwa [← h2]
  obtain ⟨u', hu'⟩ : ∃ u', u' = (e (pW hB.1 z))⁻¹ • pW hB.1 z := ⟨_, rfl⟩
  have hu'W : u' ∈ W := hu' ▸ W.smul_mem _ (pW_mem hB.1 z)
  have heu' : e u' = 1 := by rw [hu', map_smul, smul_eq_mul, inv_mul_cancel₀ hezW]
  obtain ⟨hPu', τ, hτ, hτx⟩ := hP.2 u' hu'W
  have hconj := hTr.conj hτ
  have hform : e ∘ₗ τ.symm.toLinearMap = e ∘ₗ pW hB.1 := by
    ext v
    change e (τ.symm v) = e (pW hB.1 v)
    rw [symm_apply_of_trIn hPu' hτx v, map_sub, map_smul, heu', smul_eq_mul, mul_one,
      LinearMap.comp_apply, apply_eq_pW_add_pL hB.1 e v]
    ring
  rw [hform, hτx y] at hconj
  obtain ⟨y', hy'⟩ : ∃ y', y' = y + (e ∘ₗ pL hB.1) y • u' := ⟨_, rfl⟩
  rw [← hy'] at hconj
  have heWL : ∀ l ∈ L, (e ∘ₗ pW hB.1) l = 0 := fun l hl => by
    rw [LinearMap.comp_apply, pW_of_mem_L hB.1 hl, map_zero]
  have heW0 : e ∘ₗ pW hB.1 ≠ 0 := fun h0 => hezW (by
    have := LinearMap.congr_fun h0 z
    rwa [LinearMap.comp_apply, LinearMap.zero_apply] at this)
  refine ⟨ψ, _, hψ, hB.isAminus_pL heWL heW0 hconj, ?_⟩
  have hψy' : ψ y' = ψ y := by
    rw [hy', map_add, map_smul, hψ.1 u' hu'W, smul_zero, add_zero]
  have h4 := apply_eq_pW_add_pL hB.1 ψ y'
  rw [hψ.1 _ (pW_mem hB.1 y'), zero_add, hψy'] at h4
  rw [← h4]
  exact hψy

theorem exists_of_aminus
    (hirr : ∀ X : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ X, h x ∈ X) → X = ⊥ ∨ X = ⊤)
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S)
    (hL2 : ∀ y : V, ∃ f₁ : Module.Dual (ZMod p) V, f₁ ≠ 0 ∧ (∀ l ∈ L, f₁ l = 0) ∧ f₁ y = 0)
    (hW0 : W ≠ ⊥) {l₀ : V} (hl₀ : IsAminus H L l₀) (hl₀0 : l₀ ≠ 0) :
    ∃ ψ l, IsAplus H W ψ ∧ IsAminus H L l ∧ ψ l ≠ 0 := by
  obtain ⟨S, hS, hHS⟩ := hgen
  have hQ0 : aminusSub H L ≠ ⊥ := by
    intro h
    have hl : l₀ ∈ aminusSub H L := mem_aminusSub.mpr hl₀
    rw [h] at hl
    exact hl₀0 ((Submodule.mem_bot (ZMod p)).mp hl)
  have hQt : aminusSub H L ≠ ⊤ := by
    intro h
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have hwQ : w ∈ aminusSub H L := h ▸ Submodule.mem_top
    exact hw0 (Submodule.disjoint_def.mp hB.1.disjoint w hw (mem_aminusSub.mp hwQ).1)
  obtain ⟨t, htS, y, e, hte, hyQ, q, hqQ, heq⟩ := exists_generator_moving hirr hS hHS hQ0 hQt
  rw [mem_aminusSub] at hqQ
  have hTr : TrIn H y e := TrIn.of_isTransvectionWith (hHS ▸ Subgroup.subset_closure htS) hte
  obtain ⟨f₁, hf₁0, hf₁L, hf₁y⟩ := hL2 y
  have h1 : TrIn H y f₁ := trIn_of_smul heq (TrIn.rule_R hTr (hqQ.2 f₁ hf₁L) hf₁y)
  have hyL := hB.isAminus_pL hf₁L hf₁0 h1
  have hyW : pW hB.1 y ≠ 0 := by
    intro h0
    apply hyQ
    have hy : pL hB.1 y = y := by
      have := pW_add_pL hB.1 y
      rwa [h0, zero_add] at this
    rw [mem_aminusSub, ← hy]
    exact hyL
  have hyWL : pW hB.1 y ∉ L := fun h =>
    hyW (Submodule.disjoint_def.mp hB.1.disjoint _ (pW_mem hB.1 y) h)
  obtain ⟨φ', hφ'1, hφ'L⟩ := exists_dual_one_of_notMem hyWL
  obtain ⟨hc', τ, hτ, hτx⟩ := hyL.2 (-φ') (fun l hl => by
    rw [LinearMap.neg_apply, hφ'L l hl, neg_zero])
  have hτy : τ y = pW hB.1 y := by
    rw [hτx, LinearMap.neg_apply, apply_eq_pW_add_pL hB.1 φ' y, hφ'1, hφ'L _ (pL_mem hB.1 y),
      add_zero, neg_smul, one_smul, ← sub_eq_add_neg]
    exact (eq_sub_of_add_eq (pW_add_pL hB.1 y)).symm
  have hform : e ∘ₗ τ.symm.toLinearMap = e + e (pL hB.1 y) • φ' := by
    ext v
    change e (τ.symm v) = _
    rw [symm_apply_of_trIn hc' hτx v, map_sub, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.neg_apply, smul_eq_mul, smul_eq_mul]
    ring
  have hconj := hTr.conj hτ
  rw [hτy, hform] at hconj
  have hP := hB.isAplus_comp_pL (pW_mem hB.1 y) hyW hconj
  have hPeq : (e + e (pL hB.1 y) • φ') ∘ₗ pL hB.1 = e ∘ₗ pL hB.1 := by
    ext v
    simp [hφ'L _ (pL_mem hB.1 v)]
  rw [hPeq] at hP
  refine ⟨e ∘ₗ pL hB.1, q, hP, hqQ, ?_⟩
  rw [LinearMap.comp_apply, pL_of_mem hB.1 hqQ.1]
  exact heq

end IsSLBlock

namespace IsSLBlock

variable {W L : Submodule (ZMod p) V} (hB : IsSLBlock H W L)
include hB

theorem aplus_or_aminus
    (hirr : ∀ X : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ X, h x ∈ X) → X = ⊥ ∨ X = ⊤)
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S)
    (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤)
    (hW3 : ∀ (h : Module.Dual (ZMod p) V) (x : V),
      ∃ w ∈ W, h w = 0 ∧ w ∉ Submodule.span (ZMod p) {x})
    (hL2 : ∀ y : V, ∃ f₁ : Module.Dual (ZMod p) V, f₁ ≠ 0 ∧ (∀ l ∈ L, f₁ l = 0) ∧ f₁ y = 0) :
    (∃ ψ, IsAplus H W ψ ∧ ψ ≠ 0) ∨ (∃ l, IsAminus H L l ∧ l ≠ 0) := by
  obtain ⟨S, hS, hHS⟩ := hgen
  obtain ⟨t, htS, x, h, hth, hxW, w₀, hw₀, hhw₀⟩ := exists_generator_moving hirr hS hHS hW0 hWt
  have hTr : TrIn H x h := TrIn.of_isTransvectionWith (hHS ▸ Subgroup.subset_closure htS) hth
  have hxL : pL hB.1 x ≠ 0 := by
    intro h0
    apply hxW
    have := pW_add_pL hB.1 x
    rw [h0, add_zero] at this
    rw [← this]
    exact pW_mem hB.1 x
  by_cases hhL : ∀ l ∈ L, h l = 0
  · exact Or.inr ⟨_, hB.isAminus_pL hhL hth.2.1 hTr, hxL⟩
  push Not at hhL
  obtain ⟨l₁, hl₁, hhl₁⟩ := hhL
  by_cases hxW0 : pW hB.1 x = 0
  · have hxeq : pL hB.1 x = x := by
      have := pW_add_pL hB.1 x
      rwa [hxW0, zero_add] at this
    have hxLmem : x ∈ L := hxeq ▸ pL_mem hB.1 x
    obtain ⟨φ, hφ0, hφL, hφw₀⟩ := hL2 w₀
    have h1 : TrIn H x φ :=
      trIn_of_smul hhw₀ (TrIn.rule_R hTr (hB.2 w₀ hw₀ φ hφL hφw₀) (hφL x hxLmem))
    exact Or.inr ⟨x, ⟨hxLmem, hB.trIn_axis_of_vanish hxLmem hφL hφ0 h1⟩, hth.1⟩
  · obtain ⟨w, hw, hhw, hwx⟩ := hW3 h (pW hB.1 x)
    have hxw : pW hB.1 x ∉ Submodule.span (ZMod p) {w} := by
      intro hmem
      obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hmem
      have hs0 : s ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hs
        exact hxW0 hs.symm
      exact hwx (Submodule.mem_span_singleton.mpr ⟨s⁻¹, by
        rw [← hs, smul_smul, inv_mul_cancel₀ hs0, one_smul]⟩)
    obtain ⟨φ, hφ1, hφ⟩ := exists_dual_one_of_notMem
      (notMem_sup_span_of_notMem_span hB.1.disjoint hw (pW_mem hB.1 x) hxw)
    have hφL : ∀ l ∈ L, φ l = 0 := fun l hl => hφ l (Submodule.mem_sup_left hl)
    have hφw : φ w = 0 := hφ w (Submodule.mem_sup_right (Submodule.mem_span_singleton_self w))
    have hφx : φ x = 1 := by
      rw [apply_eq_pW_add_pL hB.1 φ x, hφ1, hφL _ (pL_mem hB.1 x), add_zero]
    have h1 : TrIn H w h := by
      have := TrIn.rule_R (hB.2 w hw φ hφL hφw) hTr hhw
      rwa [hφx, one_smul] at this
    have hw0 : w ≠ 0 := fun h0 => hwx (h0 ▸ Submodule.zero_mem _)
    refine Or.inl ⟨_, hB.isAplus_comp_pL hw hw0 h1, fun h0 => hhl₁ ?_⟩
    have := LinearMap.congr_fun h0 l₁
    rwa [LinearMap.comp_apply, pL_of_mem hB.1 hl₁, LinearMap.zero_apply] at this

end IsSLBlock

theorem exists_isSLBlock_of_not_hasUniqueAxes
    (hirr : ∀ X : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ X, h x ∈ X) → X = ⊥ ∨ X = ⊤)
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S)
    (hnu : ¬ HasUniqueAxes H) :
    ∃ W L : Submodule (ZMod p) V, IsSLBlock H W L ∧ Module.finrank (ZMod p) W = 2 ∧
      ∃ ψ, IsAplus H W ψ ∧ ψ ≠ 0 := by
  unfold HasUniqueAxes at hnu
  push Not at hnu
  obtain ⟨a, f, f', ha, hf, hf', hf0, hind⟩ := hnu
  obtain ⟨b, g, φ, hφ, hg, hφb, hga⟩ := exists_partner H hirr hgen ha hf0 hf
  have hB := isSLBlock_of_reciprocal hφ hg hφb hga
  have haW : a ∈ Submodule.span (ZMod p) {a, b} := Submodule.subset_span (Set.mem_insert _ _)
  refine ⟨_, _, hB, finrank_span_pair_eq_two ha hφ.1 hφb, ?_⟩
  by_cases h1 : f ∘ₗ pL hB.1 = 0
  · by_cases h2 : f' ∘ₗ pL hB.1 = 0
    · exfalso
      have hvan : ∀ χ : Module.Dual (ZMod p) V, χ ∘ₗ pL hB.1 = 0 →
          ∀ l ∈ LinearMap.ker φ ⊓ LinearMap.ker g, χ l = 0 := by
        intro χ hχ l hl
        have := LinearMap.congr_fun hχ l
        rwa [LinearMap.comp_apply, pL_of_mem hB.1 hl, LinearMap.zero_apply] at this
      have ef := eq_comb_of_vanish hφ.1 hg.1 hφb hga (hvan f h1)
      have ef' := eq_comb_of_vanish hφ.1 hg.1 hφb hga (hvan f' h2)
      rw [hf.1, zero_div, zero_smul, add_zero] at ef
      rw [hf'.1, zero_div, zero_smul, add_zero] at ef'
      obtain ⟨s, hs⟩ : ∃ s : ZMod p, f = s • φ := ⟨_, ef⟩
      obtain ⟨s', hs'⟩ : ∃ s' : ZMod p, f' = s' • φ := ⟨_, ef'⟩
      have hs0 : s ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hs
        exact hf0 hs
      apply hind (s' / s)
      rw [hs, hs', smul_smul, div_mul_cancel₀ _ hs0]
    · exact ⟨_, hB.isAplus_comp_pL haW ha hf', h2⟩
  · exact ⟨_, hB.isAplus_comp_pL haW ha hf, h1⟩

section Finrank

variable [Module.Finite (ZMod p) V]

theorem finrank_le_finrank_inf_ker_add_one (W : Submodule (ZMod p) V)
    (e : Module.Dual (ZMod p) V) :
    Module.finrank (ZMod p) W ≤ Module.finrank (ZMod p) ↥(W ⊓ LinearMap.ker e) + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq W (LinearMap.ker e)
  have h2 := LinearMap.finrank_range_add_finrank_ker e
  have h3 : Module.finrank (ZMod p) ↥(LinearMap.range e) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range e)
    rwa [Module.finrank_self] at this
  have h4 := Submodule.finrank_le (W ⊔ LinearMap.ker e)
  omega

omit [Module.Finite (ZMod p) V] in
theorem finrank_span_singleton_le_one (x : V) :
    Module.finrank (ZMod p) (Submodule.span (ZMod p) {x}) ≤ 1 := by
  simpa using finrank_span_le_card (R := ZMod p) ({x} : Set V)

theorem exists_mem_ker_notMem_span {W : Submodule (ZMod p) V}
    (hW : 3 ≤ Module.finrank (ZMod p) W) (h : Module.Dual (ZMod p) V) (x : V) :
    ∃ w ∈ W, h w = 0 ∧ w ∉ Submodule.span (ZMod p) {x} := by
  have h1 := finrank_le_finrank_inf_ker_add_one W h
  have h2 := finrank_span_singleton_le_one (p := p) x
  by_contra hno
  push Not at hno
  have hle : W ⊓ LinearMap.ker h ≤ Submodule.span (ZMod p) {x} := fun w hw =>
    hno w (Submodule.mem_inf.mp hw).1 (LinearMap.mem_ker.mp (Submodule.mem_inf.mp hw).2)
  have := Submodule.finrank_mono hle
  omega

theorem exists_ne_zero_mem_ker {W : Submodule (ZMod p) V} (hW : 2 ≤ Module.finrank (ZMod p) W)
    (e : Module.Dual (ZMod p) V) : ∃ w ∈ W, w ≠ 0 ∧ e w = 0 := by
  have h1 := finrank_le_finrank_inf_ker_add_one W e
  have hne : W ⊓ LinearMap.ker e ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at h1
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨w, (Submodule.mem_inf.mp hw).1, hw0, LinearMap.mem_ker.mp (Submodule.mem_inf.mp hw).2⟩

theorem exists_dual_vanish {W L : Submodule (ZMod p) V} (hc : IsCompl W L)
    (hW : 2 ≤ Module.finrank (ZMod p) W) (y : V) :
    ∃ f₁ : Module.Dual (ZMod p) V, f₁ ≠ 0 ∧ (∀ l ∈ L, f₁ l = 0) ∧ f₁ y = 0 := by
  have h1 := Submodule.finrank_add_eq_of_isCompl hc
  have h2 := Submodule.finrank_add_le_finrank_add_finrank L (Submodule.span (ZMod p) {y})
  have h3 := finrank_span_singleton_le_one (p := p) y
  have hne : L ⊔ Submodule.span (ZMod p) {y} ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top] at h2
    omega
  obtain ⟨z, hz⟩ : ∃ z, z ∉ L ⊔ Submodule.span (ZMod p) {y} := by
    by_contra hno
    push Not at hno
    exact hne (eq_top_iff.mpr fun z _ => hno z)
  obtain ⟨f₁, hf₁z, hf₁⟩ := exists_dual_one_of_notMem hz
  refine ⟨f₁, fun h0 => ?_, fun l hl => hf₁ l (Submodule.mem_sup_left hl),
    hf₁ y (Submodule.mem_sup_right (Submodule.mem_span_singleton_self y))⟩
  rw [h0, LinearMap.zero_apply] at hf₁z
  exact zero_ne_one hf₁z

end Finrank

theorem forall_trIn_of_isSLBlock [Module.Finite (ZMod p) V]
    (hirr : ∀ X : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ X, h x ∈ X) → X = ⊥ ∨ X = ⊤)
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S) :
    ∀ (n : ℕ) (W L : Submodule (ZMod p) V), Module.finrank (ZMod p) L = n → IsSLBlock H W L →
      3 ≤ Module.finrank (ZMod p) W →
      ∀ (c : V) (f : Module.Dual (ZMod p) V), f c = 0 → TrIn H c f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W L hn hB hW3
  by_cases hL : L = ⊥
  · subst hL
    have hWt : W = ⊤ := by
      have := hB.1.sup_eq_top
      rwa [sup_bot_eq] at this
    intro c f hfc
    refine hB.2 c (hWt ▸ Submodule.mem_top) f (fun l hl => ?_) hfc
    rw [(Submodule.mem_bot (ZMod p)).mp hl, map_zero]
  · have hWt : W ≠ ⊤ := fun h => hL (by
      have := hB.1.inf_eq_bot
      rwa [h, top_inf_eq] at this)
    have hW0 : W ≠ ⊥ := by
      rintro rfl
      rw [finrank_bot] at hW3
      omega
    have hW2 : 2 ≤ Module.finrank (ZMod p) W := by omega
    obtain ⟨ψ, l, hψ, hl, hψl⟩ : ∃ ψ l, IsAplus H W ψ ∧ IsAminus H L l ∧ ψ l ≠ 0 := by
      rcases hB.aplus_or_aminus hirr hgen hW0 hWt (exists_mem_ker_notMem_span hW3)
          (exists_dual_vanish hB.1 hW2) with ⟨ψ₀, hψ₀, hψ₀0⟩ | ⟨l₀, hl₀, hl₀0⟩
      · exact hB.exists_of_aplus hirr hgen (exists_ne_zero_mem_ker hW2) hψ₀ hψ₀0
      · exact hB.exists_of_aminus hirr hgen (exists_dual_vanish hB.1 hW2) hW0 hl₀ hl₀0
    have hB' := hB.ystep hψ hl hψl
    have hlt : Module.finrank (ZMod p) ↥(L ⊓ LinearMap.ker ψ) < n := by
      rw [← hn]
      refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left fun h => hψl ?_)
      have : l ∈ L ⊓ LinearMap.ker ψ := by rw [h]; exact hl.1
      exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp this).2
    exact ih _ hlt _ _ rfl hB' (le_trans hW3 (Submodule.finrank_mono le_sup_left))

theorem forall_trIn_of_not_hasUniqueAxes [Module.Finite (ZMod p) V]
    (hirr : ∀ X : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ X, h x ∈ X) → X = ⊥ ∨ X = ⊤)
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S)
    (hnu : ¬ HasUniqueAxes H) :
    ∀ (c : V) (f : Module.Dual (ZMod p) V), f c = 0 → TrIn H c f := by
  obtain ⟨W, L, hB, hW2, ψ₀, hψ₀, hψ₀0⟩ := exists_isSLBlock_of_not_hasUniqueAxes hirr hgen hnu
  obtain ⟨ψ, l, hψ, hl, hψl⟩ :=
    hB.exists_of_aplus hirr hgen (exists_ne_zero_mem_ker hW2.ge) hψ₀ hψ₀0
  have hB' := hB.ystep hψ hl hψl
  have hW3 : 3 ≤ Module.finrank (ZMod p) ↥(W ⊔ Submodule.span (ZMod p) {l}) := by
    have : Module.finrank (ZMod p) W <
        Module.finrank (ZMod p) ↥(W ⊔ Submodule.span (ZMod p) {l}) := by
      refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne le_sup_left fun h => ?_)
      have hlW : l ∈ W := h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self l)
      exact hψl (hψ.1 l hlW)
    omega
  exact forall_trIn_of_isSLBlock hirr hgen _ _ _ rfl hB' hW3

theorem det_eq_one_of_mem {S : Set (V ≃ₗ[ZMod p] V)}
    (hS : ∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) (hHS : H = Subgroup.closure S)
    {g : V ≃ₗ[ZMod p] V} (hg : g ∈ H) : LinearMap.det (g : V →ₗ[ZMod p] V) = 1 := by
  have hker : H ≤ (LinearEquiv.det : (V ≃ₗ[ZMod p] V) →* (ZMod p)ˣ).ker := by
    rw [hHS]
    exact (Subgroup.closure_le _).mpr fun t ht => by
      obtain ⟨v, f, h⟩ := hS t ht
      exact isTransvectionWith_det h
  have h1 := hker hg
  rw [MonoidHom.mem_ker] at h1
  rw [← LinearEquiv.coe_det, h1]
  simp

theorem sl_of_not_hasUniqueAxes [Module.Finite (ZMod p) V] (H : Subgroup (V ≃ₗ[ZMod p] V))
    (hirr : ∀ X : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ X, h x ∈ X) → X = ⊥ ∨ X = ⊤)
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S)
    (hnu : ¬ HasUniqueAxes H) :
    ∀ g : V ≃ₗ[ZMod p] V, g ∈ H ↔ LinearMap.det (g : V →ₗ[ZMod p] V) = 1 := by
  intro g
  obtain ⟨S, hS, hHS⟩ := hgen
  exact ⟨det_eq_one_of_mem hS hHS,
    det_one_mem_of_forall_trIn H (forall_trIn_of_not_hasUniqueAxes hirr ⟨S, hS, hHS⟩ hnu) g⟩

end CFSG.StandardType.McLaughlinOdd
