module

public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Algebra.Group.Commutator

public section

namespace CFSG

namespace FiveTransitive.CommutatorSupportIntersection

open Equiv
open scoped commutatorElement

def disagreement {X : Type*} [Fintype X] [DecidableEq X] (g h : Perm X) : Finset X :=
  Finset.univ.filter (fun x => (g * h) x ≠ (h * g) x)

theorem mem_disagreement {X : Type*} [Fintype X] [DecidableEq X]
    (g h : Perm X) (x : X) : x ∈ disagreement g h ↔ g (h x) ≠ h (g x) := by
  change x ∈ Finset.univ.filter (fun y : X => (g * h) y ≠ (h * g) y) ↔ _
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, Perm.mul_apply]

theorem disagreement_subset {X : Type*} [Fintype X] [DecidableEq X]
    (g h : Perm X) :
    disagreement g h ⊆
      (g.support ∩ h.support) ∪ (g.support ∩ h.support).image (g⁻¹ : Perm X) ∪
        (g.support ∩ h.support).image (h⁻¹ : Perm X) := by
  intro x hx
  have hne := (mem_disagreement g h x).mp hx
  by_cases hg : x ∈ g.support
  · by_cases hh : x ∈ h.support
    · exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hg, hh⟩))))
    · have hhfix : h x = x := by simpa only [Perm.mem_support, not_not] using hh
      have hgs : g x ∈ g.support := Perm.apply_mem_support.mpr hg
      have hhs : g x ∈ h.support := by
        rw [Perm.mem_support]
        intro hfix
        exact hne (by rw [hhfix, hfix])
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
        (Finset.mem_image.mpr ⟨g x, Finset.mem_inter.mpr ⟨hgs, hhs⟩, g.symm_apply_apply x⟩))))
  · have hgfix : g x = x := by simpa only [Perm.mem_support, not_not] using hg
    by_cases hh : x ∈ h.support
    · have hhs : h x ∈ h.support := Perm.apply_mem_support.mpr hh
      have hgs : h x ∈ g.support := by
        rw [Perm.mem_support]
        intro hfix
        exact hne (by rw [hgfix, hfix])
      exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_image.mpr ⟨h x, Finset.mem_inter.mpr ⟨hgs, hhs⟩, h.symm_apply_apply x⟩))
    · have hhfix : h x = x := by simpa only [Perm.mem_support, not_not] using hh
      exact (hne (by simp only [hgfix, hhfix])).elim

private theorem commutator_apply_mul {X : Type*} (g h : Perm X) (x : X) :
    ⁅g, h⁆ ((h * g) x) = (g * h) x := by
  simp [commutatorElement_def, Perm.mul_apply]

theorem support_commutator_eq_image {X : Type*} [Fintype X] [DecidableEq X]
    (g h : Perm X) : ⁅g, h⁆.support = (disagreement g h).image (h * g) := by
  ext y
  constructor
  · intro hy
    refine Finset.mem_image.mpr ⟨(h * g)⁻¹ y, ?_, by simp⟩
    rw [mem_disagreement]
    have hne : ⁅g, h⁆ ((h * g) ((h * g)⁻¹ y)) ≠ (h * g) ((h * g)⁻¹ y) := by
      simpa using Perm.mem_support.mp hy
    rw [commutator_apply_mul] at hne
    exact hne
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [Perm.mem_support, commutator_apply_mul]
    exact (mem_disagreement g h x).mp hx

end FiveTransitive.CommutatorSupportIntersection

end CFSG
