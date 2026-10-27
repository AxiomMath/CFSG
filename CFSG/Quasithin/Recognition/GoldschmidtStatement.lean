module

public import CFSG.Quasithin.Recognition.GoldschmidtCompletion

public section

universe u

namespace CFSG.Quasithin

open Monoid

@[expose] def GoldschmidtEdgeBound : Prop :=
  ∀ (A C B : Type u) [Group A] [Group C] [Group B] [Finite A] [Finite C] [Finite B]
    (X : GoldAmalgam A C B), X.IsFaithful → X.IsIndexThree → Nat.card C ≤ 2 ^ 7

@[expose] def GoldschmidtEdgeBoundSubgroups : Prop :=
  ∀ (D : Type u) [Group D] (A B : Subgroup D) [Finite A] [Finite B],
    A ⊔ B = ⊤ → (A ⊓ B).relIndex A = 3 → (A ⊓ B).relIndex B = 3 →
    (∀ N : Subgroup D, N.Normal → N ≤ A ⊓ B → N = ⊥) → Nat.card (A ⊓ B : Subgroup D) ≤ 2 ^ 7

namespace GoldAmalgam

@[expose] def ofSubgroupPair {D : Type*} [Group D] (A B : Subgroup D) :
    GoldAmalgam A (A ⊓ B : Subgroup D) B where
  toA := Subgroup.inclusion inf_le_left
  toB := Subgroup.inclusion inf_le_right
  toA_injective := Subgroup.inclusion_injective _
  toB_injective := Subgroup.inclusion_injective _

@[expose] def ofSubgroupPair_completion {D : Type*} [Group D] (A B : Subgroup D)
    (hgen : A ⊔ B = ⊤) : GoldCompletion (ofSubgroupPair A B) D where
  ψA := A.subtype
  ψB := B.subtype
  ψA_injective := A.subtype_injective
  ψB_injective := B.subtype_injective
  comm _ := rfl
  gen := by rw [Subgroup.range_subtype, Subgroup.range_subtype, hgen]
  inter := by
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    intro d hd
    exact ⟨⟨d, hd⟩, rfl⟩

theorem ofSubgroupPair_edgeA_index {D : Type*} [Group D] (A B : Subgroup D) :
    (ofSubgroupPair A B).edgeA.index = (A ⊓ B).relIndex A := by
  unfold edgeA ofSubgroupPair
  rw [Subgroup.inclusion_range]
  rfl

theorem ofSubgroupPair_edgeB_index {D : Type*} [Group D] (A B : Subgroup D) :
    (ofSubgroupPair A B).edgeB.index = (A ⊓ B).relIndex B := by
  unfold edgeB ofSubgroupPair
  rw [Subgroup.inclusion_range]
  rfl

theorem ofSubgroupPair_isFaithful_iff {D : Type*} [Group D] (A B : Subgroup D) (hgen : A ⊔ B = ⊤) :
    (ofSubgroupPair A B).IsFaithful ↔ ∀ N : Subgroup D, N.Normal → N ≤ A ⊓ B → N = ⊥ := by
  rw [(ofSubgroupPair_completion A B hgen).isFaithful_iff]
  have hedge : (ofSubgroupPair_completion A B hgen).edge = A ⊓ B := by
    rw [GoldCompletion.edge_eq_inf]
    simp [ofSubgroupPair_completion]
  rw [hedge]

end GoldAmalgam

theorem goldschmidtEdgeBound_iff : GoldschmidtEdgeBound.{u} ↔ GoldschmidtEdgeBoundSubgroups.{u} := by
  constructor
  · intro h D _ A B _ _ hgen hA hB hf
    have hX := (GoldAmalgam.ofSubgroupPair_isFaithful_iff A B hgen).mpr hf
    have : Finite (A ⊓ B : Subgroup D) :=
      Finite.of_injective (Subgroup.inclusion (inf_le_left : A ⊓ B ≤ A))
        (Subgroup.inclusion_injective _)
    exact h A (A ⊓ B : Subgroup D) B (GoldAmalgam.ofSubgroupPair A B) hX
      ⟨by rw [GoldAmalgam.ofSubgroupPair_edgeA_index]; exact hA,
        by rw [GoldAmalgam.ofSubgroupPair_edgeB_index]; exact hB⟩
  · intro h A C B _ _ _ _ _ _ X hf hidx
    let Φ := X.universalCompletion
    have : Finite Φ.ψA.range :=
      Finite.of_surjective Φ.ψA.rangeRestrict Φ.ψA.rangeRestrict_surjective
    have : Finite Φ.ψB.range :=
      Finite.of_surjective Φ.ψB.rangeRestrict Φ.ψB.rangeRestrict_surjective
    have hA' : (Φ.ψA.range ⊓ Φ.ψB.range).relIndex Φ.ψA.range = 3 := by
      rw [Subgroup.inf_relIndex_left, Φ.relIndex_range_eq_edgeA_index]
      exact hidx.1
    have hB' : (Φ.ψA.range ⊓ Φ.ψB.range).relIndex Φ.ψB.range = 3 := by
      rw [Subgroup.inf_relIndex_right, Φ.relIndex_range_eq_edgeB_index]
      exact hidx.2
    have hfaith : ∀ N : Subgroup X.Universal, N.Normal → N ≤ Φ.ψA.range ⊓ Φ.ψB.range → N = ⊥ := by
      intro N hN hle
      exact (Φ.isFaithful_iff).mp hf N hN (by rwa [Φ.edge_eq_inf])
    have hbound := h X.Universal Φ.ψA.range Φ.ψB.range Φ.gen hA' hB' hfaith
    have hcard : Nat.card (Φ.ψA.range ⊓ Φ.ψB.range : Subgroup X.Universal) = Nat.card C := by
      rw [← Φ.edge_eq_inf]
      exact Φ.card_edge
    rw [hcard] at hbound
    exact hbound

end CFSG.Quasithin
