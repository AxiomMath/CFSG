module

public import Mathlib.GroupTheory.Index

import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.F918X

variable {W : Type*} [CommGroup W]

@[expose] def realized (L : Subgroup (MulAut W)) : Subgroup (MulAut ↥L) :=
  L.normalizerMonoidHom.range

theorem mem_realized {L : Subgroup (MulAut W)} {α : MulAut ↥L} :
    α ∈ realized L ↔
      ∃ g : MulAut W, ∀ l : ↥L, g * (l : MulAut W) * g⁻¹ = ((α l : ↥L) : MulAut W) := by
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    exact ⟨g, fun l => rfl⟩
  · rintro ⟨g, hg⟩
    have hmem : g ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have h1 : g * x * g⁻¹ = ((α ⟨x, hx⟩ : ↥L) : MulAut W) := hg ⟨x, hx⟩
        rw [h1]
        exact (α ⟨x, hx⟩).2
      · intro hx
        obtain ⟨l', hl'⟩ := α.surjective ⟨g * x * g⁻¹, hx⟩
        have h1 : g * (l' : MulAut W) * g⁻¹ = ((α l' : ↥L) : MulAut W) := hg l'
        rw [hl'] at h1
        have h2 : (l' : MulAut W) = x := by
          have h3 : g * (l' : MulAut W) * g⁻¹ = g * x * g⁻¹ := h1
          simpa using h3
        rw [← h2]
        exact l'.2
    refine ⟨⟨g, hmem⟩, ?_⟩
    refine MulEquiv.ext fun l => Subtype.ext ?_
    exact hg l

theorem conj_mem_realized (L : Subgroup (MulAut W)) (l : ↥L) : MulAut.conj l ∈ realized L := by
  rw [mem_realized]
  exact ⟨(l : MulAut W), fun x => by simp [MulAut.conj_apply]⟩

@[expose] def StableMod (L : Subgroup (MulAut W)) : Prop := realized L = ⊤

@[expose] def TwoClassMod (L : Subgroup (MulAut W)) : Prop := (realized L).index ≤ 2

theorem StableMod.mem_realized {L : Subgroup (MulAut W)} (h : StableMod L) (α : MulAut ↥L) :
    α ∈ realized L := by
  rw [show realized L = ⊤ from h]
  trivial

theorem StableMod.twoClass {L : Subgroup (MulAut W)} (h : StableMod L) : TwoClassMod L := by
  unfold TwoClassMod
  rw [show realized L = ⊤ from h, Subgroup.index_top]
  omega

theorem stableMod_of_forall {L : Subgroup (MulAut W)} (h : ∀ α : MulAut ↥L, α ∈ realized L) :
    StableMod L :=
  eq_top_iff.mpr fun α _ => h α

theorem twoClassMod_of_cover {L : Subgroup (MulAut W)} (γ : MulAut ↥L)
    (h : ∀ α : MulAut ↥L, α ∈ realized L ∨ γ⁻¹ * α ∈ realized L) : TwoClassMod L := by
  unfold TwoClassMod Subgroup.index
  have hsurj : Function.Surjective
      (fun b : Bool => (QuotientGroup.mk (if b then 1 else γ) : MulAut ↥L ⧸ realized L)) := by
    intro q
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective q
    rcases h α with h1 | h1
    · refine ⟨true, ?_⟩
      simp only [ite_true]
      rw [QuotientGroup.eq]
      simpa using (realized L).inv_mem h1
    · refine ⟨false, ?_⟩
      simp only [Bool.false_eq_true, ite_false]
      rw [QuotientGroup.eq]
      simpa using h1
  calc Nat.card (MulAut ↥L ⧸ realized L) ≤ Nat.card Bool := Nat.card_le_card_of_surjective _ hsurj
    _ = 2 := by simp

theorem twoClassMod_of_card {L : Subgroup (MulAut W)} [Finite (MulAut ↥L)]
    (h : Nat.card (MulAut ↥L) ≤ 2 * Nat.card (realized L)) : TwoClassMod L := by
  unfold TwoClassMod
  have h1 := (realized L).index_mul_card
  have hpos : 0 < Nat.card (realized L) := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have : 3 * Nat.card (realized L) ≤ (realized L).index * Nat.card (realized L) :=
    Nat.mul_le_mul_right _ hlt
  omega

theorem card_le_card_realized {L G : Subgroup (MulAut W)}
    (hGn : G ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hGc : ∀ g ∈ G, (∀ l ∈ L, g * l = l * g) → g = 1) [Finite (MulAut ↥L)] :
    Nat.card G ≤ Nat.card (realized L) := by
  let f : ↥G →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hGn)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hcomm : ∀ l ∈ L, (g : MulAut W) * l = l * (g : MulAut W) := by
      intro l hl
      have h1 : f g ⟨l, hl⟩ = ⟨l, hl⟩ := by rw [hg]; rfl
      have h2 : ((g : MulAut W) * l * (g : MulAut W)⁻¹) = l := congrArg Subtype.val h1
      calc (g : MulAut W) * l = (g : MulAut W) * l * (g : MulAut W)⁻¹ * (g : MulAut W) := by group
        _ = l * (g : MulAut W) := by rw [h2]
    exact Subtype.ext (hGc g g.2 hcomm)
  have hrange : ∀ g : ↥G, f g ∈ realized L := fun g => ⟨⟨g, hGn g.2⟩, rfl⟩
  let f' : ↥G →* ↥(realized L) := f.codRestrict (realized L) hrange
  have hf' : Function.Injective f' := fun a b hab =>
    hf (congrArg Subtype.val hab)
  exact Nat.card_le_card_of_injective f' hf'

theorem stableMod_of_card {L : Subgroup (MulAut W)} [Finite (MulAut ↥L)]
    (h : Nat.card (MulAut ↥L) ≤ Nat.card (realized L)) : StableMod L := by
  unfold StableMod
  exact (Subgroup.card_eq_iff_eq_top (realized L)).mp
    (le_antisymm (Subgroup.card_le_card_group _) h)

theorem twoClassMod_of_inner {L : Subgroup (MulAut W)} [Finite (MulAut ↥L)]
    (hZ : Subgroup.center ↥L = ⊥) (h : Nat.card (MulAut ↥L) ≤ 2 * Nat.card ↥L) : TwoClassMod L := by
  have hc : ∀ g ∈ L, (∀ l ∈ L, g * l = l * g) → g = 1 := by
    intro g hg hcomm
    have hmem : (⟨g, hg⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (hcomm l l.2).symm
    rw [hZ, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have h1 : Nat.card L ≤ Nat.card (realized L) :=
    card_le_card_realized (G := L) (fun g hg => Subgroup.le_normalizer hg) hc
  exact twoClassMod_of_card (by omega)

end CFSG.Quasithin.F918X
