module

public import CFSG.Permutation.FiveTransitive.CommutatorSupportIntersection

public section

namespace CFSG

namespace FiveTransitive.SymmetricCommutatorSupport

open Equiv
open scoped commutatorElement

private theorem inter_inverse_image_eq_filter
    {X : Type*} [DecidableEq X] (A : Finset X) (g : Perm X) :
    A ∩ A.image (g⁻¹ : Perm X) = A.filter (fun x => g x ∈ A) := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_filter]
  apply and_congr_right
  intro _
  constructor
  · intro hx
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
    rw [← he]
    simpa using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨g x, hx, g.symm_apply_apply x⟩

theorem card_support_commutator_add_edges_le
    {X : Type*} [Fintype X] [DecidableEq X] (g h : Perm X) :
    let A := g.support ∩ h.support
    ⁅g, h⁆.support.card + (A.filter (fun x => g x ∈ A)).card +
      (A.filter (fun x => h x ∈ A)).card ≤ 3 * A.card := by
  let A := g.support ∩ h.support
  let B := A.image (g⁻¹ : Perm X)
  let C := A.image (h⁻¹ : Perm X)
  have hc : ⁅g, h⁆.support.card = (CommutatorSupportIntersection.disagreement g h).card := by
    rw [CommutatorSupportIntersection.support_commutator_eq_image]
    exact Finset.card_image_of_injective _ (h * g).injective
  have hd := Finset.card_le_card (CommutatorSupportIntersection.disagreement_subset g h)
  change (CommutatorSupportIntersection.disagreement g h).card ≤ (A ∪ B ∪ C).card at hd
  have hb : B.card = A.card := Finset.card_image_of_injective _ (g⁻¹ : Perm X).injective
  have hh : C.card = A.card := Finset.card_image_of_injective _ (h⁻¹ : Perm X).injective
  have he₁ := Finset.card_union_add_card_inter A B
  have he₂ := Finset.card_union_add_card_inter (A ∪ B) C
  have hsub : A ∩ C ⊆ (A ∪ B) ∩ C := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_inter.mp hx).1,
      (Finset.mem_inter.mp hx).2⟩
  have hi := Finset.card_le_card hsub
  have hgfilter : (A ∩ B).card = (A.filter (fun x => g x ∈ A)).card :=
    congrArg Finset.card (inter_inverse_image_eq_filter A g)
  have hhfilter : (A ∩ C).card = (A.filter (fun x => h x ∈ A)).card :=
    congrArg Finset.card (inter_inverse_image_eq_filter A h)
  change ⁅g, h⁆.support.card + (A.filter (fun x => g x ∈ A)).card +
      (A.filter (fun x => h x ∈ A)).card ≤ 3 * A.card
  omega

end FiveTransitive.SymmetricCommutatorSupport

end CFSG
