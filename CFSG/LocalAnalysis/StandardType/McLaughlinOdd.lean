module

public import CFSG.LocalAnalysis.StandardType.McLaughlinOddSpGrow
public import CFSG.ClassicalGroups.Alternating.Generation
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.StandardType.McLaughlinOdd

open CFSG.RankThree.PartOne.LIT
open CFSG.RankThree.Classical (IsTransvectionWith)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

theorem sp_of_hasUniqueAxes [Module.Finite (ZMod p) V] (hp : p ≠ 2)
    (H : Subgroup (V ≃ₗ[ZMod p] V))
    (hirr : ∀ X : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ X, h x ∈ X) → X = ⊥ ∨ X = ⊤)
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S)
    (hua : HasUniqueAxes H)
    (hT : ∃ (a : V) (f : Module.Dual (ZMod p) V), a ≠ 0 ∧ f ≠ 0 ∧ TrIn H a f) :
    ∃ B : LinearMap.BilinForm (ZMod p) V, B.IsAlt ∧ B.Nondegenerate ∧
      ∀ g : V ≃ₗ[ZMod p] V, g ∈ H ↔ ∀ x y, B (g x) (g y) = B x y := by
  obtain ⟨β, hB⟩ := exists_isSpBlock_top hp hua hirr hgen hT
  have hgood : ∀ v, TrIn H v (β.flip v) := fun v => hB.trIn v Submodule.mem_top
  have hsep : ∀ m : V, (∀ n, β m n = 0) → m = 0 := by
    intro m hm
    by_contra hm0
    obtain ⟨w', -, hw'⟩ := hB.nondeg m Submodule.mem_top hm0
    exact hw' (hm w')
  have hβnd : β.Nondegenerate := ⟨hsep, fun m hm => hsep m fun n => by
    rw [← hB.alt.neg_eq, hm n, neg_zero]⟩
  refine ⟨β, hB.alt, hβnd, fun g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
  ·
    obtain ⟨S, hS, hHS⟩ := hgen
    rw [hHS] at hg
    refine Subgroup.closure_induction (p := fun g _ => ∀ x y, β (g x) (g y) = β x y)
      (fun t ht => ?_) (fun x y => rfl) (fun g₁ g₂ _ _ h₁ h₂ x y => ?_)
      (fun g _ hg x y => ?_) hg
    · obtain ⟨v, f, hvf⟩ := hS t ht
      have htH : t ∈ H := hHS ▸ Subgroup.subset_closure ht
      obtain ⟨s, hs⟩ := hua v (β.flip v) f hvf.1 (hgood v)
        (TrIn.of_isTransvectionWith htH hvf) (hB.flip_ne_zero Submodule.mem_top hvf.1)
      have htz : ∀ z, t z = z + (s * β z v) • v := fun z => by
        rw [hvf.2.2.2 z, hs, LinearMap.smul_apply, LinearMap.BilinForm.flip_apply, smul_eq_mul]
      intro z w
      have hneg : -β v w = β w v := hB.alt.neg_eq v w
      rw [htz z, htz w]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hB.alt.self_eq_zero v]
      linear_combination (-(s * β z v)) * hneg
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, h₁, h₂]
    · have := hg (g⁻¹ x) (g⁻¹ y)
      rw [show g (g⁻¹ x) = x from LinearEquiv.apply_symm_apply g x,
        show g (g⁻¹ y) = y from LinearEquiv.apply_symm_apply g y] at this
      exact this.symm
  ·
    let e := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) V
    have hmem : e.symm g ∈ CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup β :=
      fun x y => hg x y
    rw [CFSG.ClassicalGroups.Alternating.alternating_transvection_generation hB.alt hβnd] at hmem
    have hle : Subgroup.closure {t | ∃ (a : V) (c : ZMod p),
        t = CFSG.ClassicalGroups.Alternating.symplecticTransvection β hB.alt a c} ≤
        H.map e.symm.toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro _ ⟨a, c, rfl⟩
      obtain ⟨-, t, ht, htx⟩ := (hgood a).smul c
      refine ⟨t, ht, ?_⟩
      refine Units.ext (LinearMap.ext fun x => ?_)
      change t x = _
      rw [htx, CFSG.ClassicalGroups.Alternating.symplecticTransvection_apply,
        LinearMap.smul_apply, LinearMap.BilinForm.flip_apply, smul_eq_mul]
    obtain ⟨t, ht, hte⟩ := hle hmem
    have htg : t = g := e.symm.injective hte
    exact htg ▸ ht

theorem forall_trIn_of_no_transvection (H : Subgroup (V ≃ₗ[ZMod p] V))
    (hirr : ∀ X : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ X, h x ∈ X) → X = ⊥ ∨ X = ⊤)
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S)
    (hT : ¬ ∃ (a : V) (f : Module.Dual (ZMod p) V), a ≠ 0 ∧ f ≠ 0 ∧ TrIn H a f) :
    ∀ (c : V) (f : Module.Dual (ZMod p) V), f c = 0 → TrIn H c f := by
  intro c f hfc
  by_cases hc : c = 0
  · rw [hc]
    exact TrIn.zero_center f
  by_cases hf : f = 0
  · rw [hf]
    exact TrIn.zero_axis c
  exfalso
  obtain ⟨S, hS, hHS⟩ := hgen
  have hS0 : S = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun t ht => hT ?_
    obtain ⟨v, g, hvg⟩ := hS t ht
    exact ⟨v, g, hvg.1, hvg.2.1,
      TrIn.of_isTransvectionWith (hHS ▸ Subgroup.subset_closure ht) hvg⟩
  have hH : H = ⊥ := by rw [hHS, hS0, Subgroup.closure_empty]
  rcases hirr (Submodule.span (ZMod p) {c}) (fun h hh y hy => by
      rw [hH, Subgroup.mem_bot] at hh
      rw [hh]
      exact hy) with h | h
  · exact hc (Submodule.span_singleton_eq_bot.mp h)
  · apply hf
    refine LinearMap.ext fun x => ?_
    have hx : x ∈ Submodule.span (ZMod p) {c} := by rw [h]; exact Submodule.mem_top
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, hfc, smul_zero, LinearMap.zero_apply]

theorem mcLaughlin_odd {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] (H : Subgroup (V ≃ₗ[ZMod p] V))
    (hirr : ∀ W : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ W, h x ∈ W) → W = ⊥ ∨ W = ⊤)
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S) :
    (∀ g : V ≃ₗ[ZMod p] V, g ∈ H ↔ LinearMap.det (g : V →ₗ[ZMod p] V) = 1) ∨
    (∃ B : LinearMap.BilinForm (ZMod p) V, B.IsAlt ∧ B.Nondegenerate ∧
      ∀ g : V ≃ₗ[ZMod p] V, g ∈ H ↔ ∀ x y, B (g x) (g y) = B x y) := by
  by_cases hua : HasUniqueAxes H
  · by_cases hT : ∃ (a : V) (f : Module.Dual (ZMod p) V), a ≠ 0 ∧ f ≠ 0 ∧ TrIn H a f
    · exact Or.inr (sp_of_hasUniqueAxes hp H hirr hgen hua hT)
    · left
      intro g
      obtain ⟨S, hS, hHS⟩ := hgen
      exact ⟨det_eq_one_of_mem hS hHS, det_one_mem_of_forall_trIn H
        (forall_trIn_of_no_transvection H hirr ⟨S, hS, hHS⟩ hT) g⟩
  · exact Or.inl (sl_of_not_hasUniqueAxes H hirr hgen hua)

end CFSG.StandardType.McLaughlinOdd
