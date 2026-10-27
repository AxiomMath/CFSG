module

public import Mathlib.GroupTheory.Perm.Support

public section

namespace CFSG

namespace FiveTransitive.ManningEdgeGeometry

open Equiv

private theorem mem_inverse_image {X : Type*} [DecidableEq X]
    (g : Perm X) (S : Finset X) (x : X) :
    x ∈ S.image g.symm ↔ g x ∈ S := by
  constructor
  · intro h
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h
    simpa using hy
  · intro h
    exact Finset.mem_image.mpr ⟨g x,h,g.symm_apply_apply x⟩

theorem outer_edges_card_identity
    {X : Type*} [Fintype X] [DecidableEq X]
    (g : Perm X) (S : Finset X) (hS : S ⊆ g.support) :
    (g.support.filter (fun x => x ∉ S ∧ g x ∉ S)).card + 2*S.card =
      g.support.card + (S.filter (fun x => g x ∈ S)).card := by
  let U := S ∪ S.image g.symm
  have hU : U ⊆ g.support := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hS hx
    · have h := hS ((mem_inverse_image g S x).mp hx)
      exact Perm.apply_mem_support.mp h
  have hB : g.support.filter (fun x => x ∉ S ∧ g x ∉ S) = g.support \ U := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_sdiff, U, Finset.mem_union,
      mem_inverse_image, not_or]
  have hI : S ∩ S.image g.symm = S.filter (fun x => g x ∈ S) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter, mem_inverse_image]
  have hcard := Finset.card_union_add_card_inter S (S.image g.symm)
  have hpre : (S.image g.symm).card = S.card := Finset.card_image_of_injective _ g.symm.injective
  have hdiff := Finset.card_sdiff_add_card_eq_card hU
  rw [hI,hpre] at hcard
  rw [hB]
  change (g.support \ U).card + 2*S.card = _
  change U.card + _ = _ at hcard
  omega

theorem outer_edges_card_of_no_internal
    {X : Type*} [Fintype X] [DecidableEq X]
    (g : Perm X) (S : Finset X) (hS : S ⊆ g.support)
    (hn : ∀ x ∈ S, g x ∉ S) :
    (g.support.filter (fun x => x ∉ S ∧ g x ∉ S)).card = g.support.card - 2*S.card := by
  have he : S.filter (fun x => g x ∈ S) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hn x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
  have h := outer_edges_card_identity g S hS
  rw [he,Finset.card_empty] at h
  omega

private theorem distinguished_edges_eq_pair
    {X : Type*} [Fintype X] [DecidableEq X]
    (g : Perm X) (S : Finset X) {c : X} (hc : c ∈ S) (hcs : c ∈ g.support)
    (hpost : g c ∉ S) (hpre : g.symm c ∉ S) :
    g.support.filter (fun x => (x=c ∧ g x ∉ S) ∨ (x∉S ∧ g x=c)) =
      {c,g.symm c} := by
  have hpres : g.symm c ∈ g.support := Perm.apply_mem_support.mp (by simpa using hcs)
  ext x
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨_, ⟨rfl,_⟩ | ⟨_,hx⟩⟩
    · exact Or.inl rfl
    · exact Or.inr (g.injective (hx.trans (g.apply_symm_apply c).symm))
  · rintro (rfl | rfl)
    · exact ⟨hcs,Or.inl ⟨rfl,hpost⟩⟩
    · exact ⟨hpres,Or.inr ⟨hpre,g.apply_symm_apply c⟩⟩

theorem distinguished_edges_card_two
    {X : Type*} [Fintype X] [DecidableEq X]
    (g : Perm X) (S : Finset X) {c : X} (hc : c ∈ S) (hcs : c ∈ g.support)
    (hpost : g c ∉ S) (hpre : g.symm c ∉ S) :
    (g.support.filter (fun x => (x=c ∧ g x ∉ S) ∨ (x∉S ∧ g x=c))).card = 2 := by
  rw [distinguished_edges_eq_pair g S hc hcs hpost hpre, Finset.card_pair]
  intro he
  exact hpre (he ▸ hc)

theorem distinguished_edges_card_one
    {X : Type*} [Fintype X] [DecidableEq X]
    (g : Perm X) (S : Finset X) {c : X} (hcs : c ∈ g.support)
    (hpost : g c ∈ S) (hpre : g.symm c ∉ S) :
    (g.support.filter (fun x => (x=c ∧ g x ∉ S) ∨ (x∉S ∧ g x=c))).card = 1 := by
  have hpres : g.symm c ∈ g.support := Perm.apply_mem_support.mp (by simpa using hcs)
  have he : g.support.filter (fun x => (x=c ∧ g x ∉ S) ∨ (x∉S ∧ g x=c)) =
      {g.symm c} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, ⟨rfl,hn⟩ | ⟨_,hx⟩⟩
      · exact (hn hpost).elim
      · exact g.injective (hx.trans (g.apply_symm_apply c).symm)
    · rintro rfl
      exact ⟨hpres,Or.inr ⟨hpre,g.apply_symm_apply c⟩⟩
  rw [he,Finset.card_singleton]

end FiveTransitive.ManningEdgeGeometry

end CFSG
