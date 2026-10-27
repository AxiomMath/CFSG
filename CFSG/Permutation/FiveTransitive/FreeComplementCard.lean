module

public import Mathlib.GroupTheory.GroupAction.CardCommute
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Data.Set.Card

public section

namespace CFSG

namespace FiveTransitive.FreeComplementCard

open MulAction
open scoped BigOperators

theorem card_dvd_of_free
    (Q C : Type*) [Group Q] [Finite Q] [Finite C] [MulAction Q C]
    (hfree : ∀ q : Q, ∀ x : C, q • x = x → q = 1) :
    Nat.card Q ∣ Nat.card C := by
  classical
  let _ : Fintype Q := Fintype.ofFinite Q
  let _ : Fintype C := Fintype.ofFinite C
  let _ : Fintype (Quotient (orbitRel Q C)) := Fintype.ofFinite _
  let _ : ∀ x : C, Fintype (stabilizer Q x) := fun _ => Fintype.ofFinite _
  have hcardstab (x : C) : Fintype.card (stabilizer Q x) = 1 := by
    let _ : Subsingleton (stabilizer Q x) :=
      ⟨fun a b => Subtype.ext ((hfree a x a.property).trans (hfree b x b.property).symm)⟩
    exact Fintype.card_eq_one_iff.mpr ⟨1, fun _ => Subsingleton.elim _ _⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    card_eq_sum_card_group_div_card_stabilizer Q C]
  simp only [hcardstab, Nat.div_one, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  exact dvd_mul_left _ _

theorem card_dvd_complement
    (Q X : Type*) [Group Q] [Finite Q] [Finite X] [MulAction Q X]
    (S : Set X) (hstable : ∀ q : Q, ∀ x ∈ S, q • x ∈ S)
    (hfree : ∀ q : Q, ∀ x : X, x ∉ S → q • x = x → q = 1) :
    Nat.card Q ∣ Nat.card X - S.ncard := by
  let C : SubMulAction Q X :=
    { carrier := Sᶜ
      smul_mem' := by
        intro q x hx
        change x ∉ S at hx
        change q • x ∉ S
        intro hqx
        exact hx (by simpa only [inv_smul_smul] using hstable q⁻¹ (q • x) hqx) }
  have hc : Nat.card Q ∣ Nat.card C := card_dvd_of_free Q C (by
    intro q x hqx
    exact hfree q x x.property (congrArg Subtype.val hqx))
  change Nat.card Q ∣ Nat.card (Sᶜ : Set X) at hc
  rwa [Nat.card_coe_set_eq, Set.ncard_compl] at hc

end FiveTransitive.FreeComplementCard

end CFSG
