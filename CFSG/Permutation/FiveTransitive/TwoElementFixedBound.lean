module

public import CFSG.Permutation.FiveTransitive.TwoRootEven

public section

namespace CFSG

namespace FiveTransitive.TwoElementFixedBound

open Equiv Function CyclePatternRoots

theorem fixed_square_card {X : Type*} [Finite X] (g : Perm X) :
    Nat.card (Function.fixedPoints g) + Nat.card (TwoRoot g) =
      Nat.card (Function.fixedPoints (g ^ 2 : Perm X)) := by
  let A := Function.fixedPoints g
  let B : Set X := {x | g (g x) = x ∧ g x ≠ x}
  have hd : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x ha hb
    exact hb.2 ha
  have hu : A ∪ B = Function.fixedPoints (g ^ 2 : Perm X) := by
    ext x
    change (g x = x ∨ (g (g x) = x ∧ g x ≠ x)) ↔ g (g x) = x
    constructor
    · rintro (h | h)
      · rw [h,h]
      · exact h.1
    · intro h
      by_cases hx : g x = x
      · exact Or.inl hx
      · exact Or.inr ⟨h,hx⟩
  have h := Set.ncard_union_eq hd
  rw [hu] at h
  let e : TwoRoot g ≃ B :=
    { toFun := fun x => ⟨x.val, x.property⟩
      invFun := fun x => ⟨x.val, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_coe_set_eq, Nat.card_coe_set_eq,
    Nat.card_coe_set_eq]
  exact h.symm

theorem fixed_add_two_card_le_six
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hinv : ∀ u : G, orderOf u = 2 →
      Nat.card (Function.fixedPoints (MulAction.toPerm u : Perm X)) ≤ 6)
    (a : G) (k : ℕ) (hk : 2 ≤ k) (ho : orderOf a = 2 ^ k) :
    Nat.card (Function.fixedPoints (MulAction.toPerm a : Perm X)) +
      Nat.card (TwoRoot (MulAction.toPerm a : Perm X)) ≤ 6 := by
  obtain ⟨l,rfl⟩ : ∃ l, k = l + 2 := ⟨k - 2, by omega⟩
  let b := a ^ (2 ^ (l + 1))
  have hn : 2 ^ (l + 1) ≠ (0 : ℕ) := pow_ne_zero _ (by decide)
  have hd : 2 ^ (l + 1) ∣ orderOf a := ⟨2, by rw [ho, pow_succ]⟩
  have hob : orderOf b = 2 := by
    change orderOf (a ^ (2 ^ (l + 1))) = 2
    rw [orderOf_pow_of_dvd hn hd, ho, pow_succ]
    exact Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn)
  have hsub : Function.fixedPoints ((MulAction.toPerm a : Perm X) ^ 2 : Perm X) ⊆
      Function.fixedPoints (MulAction.toPerm b : Perm X) := by
    intro x hx
    have hp : IsPeriodicPt (MulAction.toPerm a : Perm X) 2 x := hx
    have hm := hp.mul_const (2 ^ l)
    change ((MulAction.toPermHom G X) (a ^ (2 ^ (l + 1)))) x = x
    rw [map_pow, pow_succ, Nat.mul_comm, ← Perm.iterate_eq_pow]
    exact hm
  rw [fixed_square_card]
  calc
    _ ≤ Nat.card (Function.fixedPoints (MulAction.toPerm b : Perm X)) := by
      rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq]
      exact Set.ncard_le_ncard hsub
    _ ≤ 6 := hinv b hob

theorem two_card_eq_two_or_four
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hinv : ∀ u : G, orderOf u = 2 →
      Nat.card (Function.fixedPoints (MulAction.toPerm u : Perm X)) ≤ 6)
    (a : G) (k : ℕ) (hk : 2 ≤ k) (ho : orderOf a = 2 ^ k)
    (hlo : 2 ≤ Nat.card (TwoRoot (MulAction.toPerm a : Perm X)))
    (hfix : 4 ≤ Nat.card (TwoRoot (MulAction.toPerm a : Perm X)) →
      2 ≤ Nat.card (Function.fixedPoints (MulAction.toPerm a : Perm X))) :
    Nat.card (TwoRoot (MulAction.toPerm a : Perm X)) = 2 ∨
      Nat.card (TwoRoot (MulAction.toPerm a : Perm X)) = 4 := by
  have hb := fixed_add_two_card_le_six hinv a k hk ho
  have he := Nat.even_iff.mp (TwoRootEven.even_two_card (MulAction.toPerm a : Perm X))
  omega

end FiveTransitive.TwoElementFixedBound

end CFSG
