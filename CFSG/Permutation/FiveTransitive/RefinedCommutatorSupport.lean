module

public import CFSG.Permutation.FiveTransitive.CommutatorSupportIntersection

public section

namespace CFSG

namespace FiveTransitive.RefinedCommutatorSupport

open Equiv
open scoped commutatorElement

def outsideEntry {X : Type*} [Fintype X] [DecidableEq X]
    (g h : Perm X) : Finset X :=
  Finset.univ.filter (fun x => x ∉ g.support ∧ h x ∈ g.support)

def fixedMovedImage {X : Type*} [Fintype X] [DecidableEq X]
    (g h : Perm X) : Finset X :=
  Finset.univ.filter (fun x => x ∈ g.support ∧ h x = x ∧ g x ∈ h.support)

@[simp] theorem mem_outsideEntry {X : Type*} [Fintype X] [DecidableEq X]
    (g h : Perm X) (x : X) :
    x ∈ outsideEntry g h ↔ x ∉ g.support ∧ h x ∈ g.support := by
  simp only [outsideEntry, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem mem_fixedMovedImage {X : Type*} [Fintype X] [DecidableEq X]
    (g h : Perm X) (x : X) :
    x ∈ fixedMovedImage g h ↔ x ∈ g.support ∧ h x = x ∧ g x ∈ h.support := by
  simp only [fixedMovedImage, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem disagreement_subset {X : Type*} [Fintype X] [DecidableEq X]
    (g h : Perm X) :
    CommutatorSupportIntersection.disagreement g h ⊆
      (g.support ∩ h.support) ∪ outsideEntry g h ∪ fixedMovedImage g h := by
  intro x hx
  have hne := (CommutatorSupportIntersection.mem_disagreement g h x).mp hx
  by_cases hg : x ∈ g.support
  · by_cases hh : x ∈ h.support
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (Finset.mem_inter.mpr ⟨hg, hh⟩))))
    · have hhfix : h x = x := by simpa only [Perm.mem_support, not_not] using hh
      have hhs : g x ∈ h.support := by
        rw [Perm.mem_support]
        intro hfix
        exact hne (by rw [hhfix, hfix])
      exact Finset.mem_union.mpr (Or.inr
        ((mem_fixedMovedImage g h x).mpr ⟨hg, hhfix, hhs⟩))
  · have hgfix : g x = x := by simpa only [Perm.mem_support, not_not] using hg
    have hgs : h x ∈ g.support := by
      rw [Perm.mem_support]
      intro hfix
      exact hne (by rw [hgfix, hfix])
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
      (Or.inr ((mem_outsideEntry g h x).mpr ⟨hg, hgs⟩))))

theorem card_support_commutator_le {X : Type*} [Fintype X] [DecidableEq X]
    (g h : Perm X) :
    ⁅g, h⁆.support.card ≤ (g.support ∩ h.support).card +
      (outsideEntry g h).card + (fixedMovedImage g h).card := by
  have hcard : ⁅g, h⁆.support.card =
      (CommutatorSupportIntersection.disagreement g h).card := by
    rw [CommutatorSupportIntersection.support_commutator_eq_image]
    exact Finset.card_image_of_injective _ (h * g).injective
  have hsub := Finset.card_le_card (disagreement_subset g h)
  have houter := Finset.card_union_le
    ((g.support ∩ h.support) ∪ outsideEntry g h) (fixedMovedImage g h)
  have hinner := Finset.card_union_le (g.support ∩ h.support) (outsideEntry g h)
  omega

theorem not_commute_of_fixed_moved_image {X : Type*}
    (g h : Perm X) (x : X) (hfix : h x = x) (hmove : h (g x) ≠ g x) :
    ¬ Commute g h := by
  intro hcomm
  have heq := congrArg (fun q : Perm X => q x) hcomm.eq
  simp only [Perm.mul_apply, hfix] at heq
  exact hmove heq.symm

end FiveTransitive.RefinedCommutatorSupport

end CFSG
