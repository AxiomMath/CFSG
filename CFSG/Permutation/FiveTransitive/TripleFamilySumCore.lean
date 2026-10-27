module

public import CFSG.Permutation.FiveTransitive.FamilyCommutatorAverage

public section

namespace CFSG

namespace FiveTransitive.TripleFamilySumCore
open Equiv
open scoped BigOperators

theorem card_pred_congr {T : Type*} (p q : T → Prop)
    (h : ∀ t, p t ↔ q t) : Nat.card {t // p t} = Nat.card {t // q t} :=
  Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl T) h)

private theorem sum_card_filter_mul_eq {T X : Type*} [Fintype T] [Fintype X]
    (A : Finset X) (p : T → X → Prop) [∀ t x, Decidable (p t x)] (d b : ℕ)
    (h : ∀ x ∈ A, Nat.card {t : T // p t x} * d = b) :
    (∑ t : T, (A.filter (p t)).card) * d = A.card * b := by
  rw [FamilyCommutatorAverage.sum_card_filter, Finset.sum_mul]
  calc
    _ = ∑ x ∈ A, b := Finset.sum_congr rfl h
    _ = _ := by simp

@[expose] def intersection {X : Type*} [Fintype X] [DecidableEq X] (g v : Perm X) : Finset X :=
  g.support ∩ v.support

@[expose] def qCount {X : Type*} [Fintype X] [DecidableEq X] (g v : Perm X) : ℕ :=
  ((intersection g v).filter fun x => g x ∈ intersection g v).card

@[expose] def rCount {X : Type*} [Fintype X] [DecidableEq X] (g v : Perm X) : ℕ :=
  ((intersection g v).filter fun x => v x ∈ intersection g v).card

@[expose] def outerEdges {X : Type*} [Fintype X] [DecidableEq X] (g : Perm X) (S : Finset X) : Finset X :=
  g.support.filter fun x => x ∉ S ∧ g x ∉ S

@[expose] def distinguishedEdges {X : Type*} [Fintype X] [DecidableEq X]
    (g : Perm X) (S : Finset X) (c : X) : Finset X :=
  g.support.filter fun x => (x = c ∧ g x ∉ S) ∨ (x ∉ S ∧ g x = c)

private theorem intersection_eq_insert {X : Type*} [Fintype X] [DecidableEq X]
    (g v : Perm X) (S : Finset X) (c : X) (hS : S ⊆ g.support) (hc : c ∈ S)
    (hmove : v c ≠ c) (hfix : ∀ x ∈ S, x ≠ c → v x = x) :
    intersection g v = insert c ((g.support \ S).filter fun x => v x ≠ x) := by
  ext x
  simp only [intersection, Finset.mem_inter, Perm.mem_support, Finset.mem_insert,
    Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨hg, hv⟩
    by_cases he : x = c
    · exact Or.inl he
    · exact Or.inr ⟨⟨hg, fun hx => hv (hfix x hx he)⟩, hv⟩
  · rintro (rfl | ⟨⟨hg, _⟩, hv⟩)
    · exact ⟨Perm.mem_support.mp (hS hc), hmove⟩
    · exact ⟨hg, hv⟩

theorem sum_intersection
    {T X : Type*} [Fintype T] [Fintype X] [DecidableEq X]
    (g : Perm X) (S : Finset X) (c : X) (hS : S ⊆ g.support) (hScard : S.card = 3) (hc : c ∈ S)
    (v : T → Perm X) (hmove : ∀ t, v t c ≠ c) (hfix : ∀ t x, x ∈ S → x ≠ c → v t x = x)
    (hpoint : ∀ x, x ∉ S → Nat.card {t : T // v t x ≠ x} * (Fintype.card X - 3) =
      Nat.card T * (g.support.card - 1)) :
    (∑ t : T, (intersection g (v t)).card) * (Fintype.card X - 3) =
      Nat.card T * (Fintype.card X - 3) + Nat.card T * (g.support.card - 1) * (g.support.card - 3) := by
  classical
  let O := g.support \ S
  have hO : O.card = g.support.card - 3 := by rw [Finset.card_sdiff_of_subset hS, hScard]
  have hcard (t : T) : (intersection g (v t)).card = 1 + (O.filter fun x => v t x ≠ x).card := by
    rw [intersection_eq_insert g (v t) S c hS hc (hmove t) (hfix t)]
    rw [Finset.card_insert_of_notMem (by simp [hc])]
    change (O.filter fun x => v t x ≠ x).card + 1 = 1 + (O.filter fun x => v t x ≠ x).card
    omega
  have hsum := sum_card_filter_mul_eq O (fun t x => v t x ≠ x) (Fintype.card X - 3)
    (Nat.card T * (g.support.card - 1)) (fun x hx => hpoint x (Finset.mem_sdiff.mp hx).2)
  simp only [hcard, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  rw [← Nat.card_eq_fintype_card, add_mul, hsum, hO]
  ac_rfl

end FiveTransitive.TripleFamilySumCore

end CFSG
