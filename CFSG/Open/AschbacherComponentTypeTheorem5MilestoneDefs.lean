module

public import CFSG.Open.Defs

public section

namespace CFSG.Open
@[expose] def aschbacherThm5OddCore (H : Type*) [Group H] : Subgroup H :=
  sSup {N : Subgroup H | N.Normal ∧ Odd (Nat.card N)}

instance aschbacherThm5OddCore_normal (H : Type*) [Group H] :
    (aschbacherThm5OddCore H).Normal :=
  Subgroup.sSup_normal _ fun _ hN => hN.1

@[expose] def aschbacherThm5Core {G : Type*} [Group G] (D : Subgroup G) : Subgroup G :=
  (aschbacherThm5OddCore D).map D.subtype

@[expose] def aschbacherThm5Preimage {G : Type*} [Group G] (D : Subgroup G)
    (Abar : Subgroup (D ⧸ aschbacherThm5OddCore D)) : Subgroup G :=
  (Abar.comap (QuotientGroup.mk' (aschbacherThm5OddCore D))).map D.subtype

@[expose] def aschbacherThm5Centralizes {G : Type*} [Group G] (O A : Subgroup G) (y : G) : Prop :=
  ∀ a ∈ A, y⁻¹ * a⁻¹ * y * a ∈ O

@[expose] def aschbacherThm5IsSemisimple {Q : Type*} [Group Q] (X : Subgroup Q) : Prop :=
  ∃ (k : ℕ) (K : Fin k → Subgroup Q), 0 < k ∧
    (∀ l, K l ≤ X ∧ IsQuasisimple (K l)) ∧
    (∀ l m, l ≠ m → ∀ x ∈ K l, ∀ y ∈ K m, x * y = y * x) ∧
    ⨆ l, K l = X

end CFSG.Open
