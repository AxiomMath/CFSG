module

public import Mathlib
public import CFSG.Open.Defs
public import CFSG.Foundations.FullStandardCore

public section

namespace CFSG.Open

@[expose] def standardComponentIsStandard {G : Type*} [Group G] (L : Subgroup G) : Prop :=
  full_standard% FullStandardCore (IsQuasisimple L)
    (fun H g => H.map (MulAut.conj g).toMonoidHom) L

theorem standardComponentIsStandard_eq_fullStandardCore {G : Type*} [Group G] (L : Subgroup G) :
    standardComponentIsStandard L =
      FullStandardCore (IsQuasisimple L) (fun H g => H.map (MulAut.conj g).toMonoidHom) L :=
  rfl

@[expose] def standardComponentOddCore (H : Type*) [Group H] : Subgroup H :=
  sSup {N : Subgroup H | N.Normal ∧ Odd (Nat.card N)}

@[expose] def standardComponentOrderHe : ℕ := 2 ^ 10 * 3 ^ 3 * 5 ^ 2 * 7 ^ 3 * 17

@[expose] def standardComponentOrderM12 : ℕ := 2 ^ 6 * 3 ^ 3 * 5 * 11

@[expose] def standardComponentOrderJ2 : ℕ := 2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7

@[expose] def standardComponentOddSporadicOrders : Set ℕ :=
  {standardComponentOrderM12, 2 ^ 3 * 3 * 5 * 7 * 11 * 19, standardComponentOrderJ2,
    2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11, 2 ^ 7 * 3 ^ 6 * 5 ^ 3 * 7 * 11,
    2 ^ 8 * 3 ^ 7 * 5 ^ 6 * 7 * 11 * 31 * 37 * 67, 2 ^ 13 * 3 ^ 7 * 5 ^ 2 * 7 * 11 * 13,
    standardComponentOrderHe, 2 ^ 9 * 3 ^ 4 * 5 * 7 ^ 3 * 11 * 19 * 31}

@[expose] def standardComponentRankTwoSporadicOrders : Set ℕ :=
  {standardComponentOrderJ2, 2 ^ 13 * 3 ^ 7 * 5 ^ 2 * 7 * 11 * 13, standardComponentOrderHe,
    2 ^ 14 * 3 ^ 3 * 5 ^ 3 * 7 * 13 * 29, 2 ^ 21 * 3 ^ 9 * 5 ^ 4 * 7 ^ 2 * 11 * 13 * 23}

@[expose] def standardComponentEvenSporadicOrders : Set ℕ :=
  {2 ^ 10 * 3 ^ 7 * 5 ^ 3 * 7 * 11 * 23, 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19,
    2 ^ 17 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13, 2 ^ 18 * 3 ^ 13 * 5 ^ 2 * 7 * 11 * 13 * 17 * 23,
    2 ^ 21 * 3 ^ 16 * 5 ^ 2 * 7 ^ 3 * 11 * 13 * 17 * 23 * 29,
    2 ^ 41 * 3 ^ 13 * 5 ^ 6 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 31 * 47,
    2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 *
      71}

@[expose] def standardComponentOddType (X : Type*) [Group X] : Prop :=
  (∃ n : ℕ, 5 ≤ n ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
    (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card X ∈ lieOrdersChar p) ∨
    Nat.card X = ordA 2 4 ∨ Nat.card X = standardComponentOrderHe

@[expose] def standardComponentEvenType (X : Type*) [Group X] : Prop :=
  Nat.card X ∈ lieOrdersChar 2 ∨ Nat.card X ∈ (sporadicOrderList : Set ℕ)

@[expose] def standardComponentEvenException (X : Type*) [Group X] : Prop :=
  Nat.card X ∈ ({ordA 1 4, ordA 2 2, ordA 3 2, 360, 6048, ordTwistedA 3 2, ordA 2 4,
    standardComponentOrderHe} : Set ℕ)

@[expose] def standardComponentResidualA (L : Type*) [Group L] : Prop :=
  Nat.card (L ⧸ Subgroup.center L) ∈ (sporadicOrderList : Set ℕ) ∧
    Nat.card (L ⧸ Subgroup.center L) ≠ standardComponentOrderHe

@[expose] def standardComponentResidualB (L : Type*) [Group L] : Prop :=
  Nat.card (Subgroup.center L) = 2 ∧
    Nat.card (L ⧸ Subgroup.center L) ∈ ({ordG2 4, ordF4 2, ordTwistedE6 2} : Set ℕ)

@[expose] def standardComponentResidualC (L : Type*) [Group L] : Prop :=
  Nat.card (L ⧸ Subgroup.center L) ∈ ({ordBC 3 2, ordTwistedA 5 2, ordD 4 2} : Set ℕ)

@[expose] def standardComponentResidualD (L : Type*) [Group L] : Prop :=
  Subgroup.center L = ⊥ ∧ Nat.card L = ordTwistedD 4 2

@[expose] def standardComponentEvenResidual (L : Type*) [Group L] : Prop :=
  IsPGroup 2 (Subgroup.center L) ∧
    (standardComponentResidualA L ∨ standardComponentResidualB L ∨
      standardComponentResidualC L ∨ standardComponentResidualD L)

@[expose] def standardComponentEvenBNRankTwoOrders : Set ℕ :=
  {m | ∃ f : ℕ, 1 ≤ f ∧
      (m = ordA 2 (2 ^ f) ∨ m = ordTwistedA 3 (2 ^ f) ∨ m = ordTwistedA 4 (2 ^ f) ∨
        (2 ≤ f ∧ m = ordBC 2 (2 ^ f)) ∨ (2 ≤ f ∧ m = ordG2 (2 ^ f)) ∨
        m = ordTrialityD4 (2 ^ f))} ∪
    {m | ∃ k : ℕ, 1 ≤ k ∧ m = ordTwistedF4 (2 ^ (2 * k + 1))} ∪ {ordTits}

end CFSG.Open
