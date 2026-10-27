module

public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace CFSG

theorem eq_bot_or_eq_top_of_normal {G : Type*} [Group G] [IsSimpleGroup G]
    (H : Subgroup G) (hH : H.Normal) : H = ⊥ ∨ H = ⊤ := by
  let := hH
  exact IsSimpleGroup.eq_bot_or_eq_top_of_normal H

theorem subgroup_isMulCommutative_closure {G : Type*} [Group G] {s : Set G}
    (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) : IsMulCommutative (Subgroup.closure s) :=
  Subgroup.isMulCommutative_closure (fun a ha b hb _ => hcomm a ha b hb)

theorem subring_isMulCommutative_closure {R : Type*} [Ring R] {s : Set R}
    (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) : IsMulCommutative (Subring.closure s) :=
  Subring.isMulCommutative_closure (fun a ha b hb _ => hcomm a ha b hb)

theorem card_dvd_of_surjective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) : Nat.card H ∣ Nat.card G :=
  Subgroup.card_dvd_of_surjective hf

end CFSG
