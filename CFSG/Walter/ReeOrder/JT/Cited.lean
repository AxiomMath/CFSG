module

public import CFSG.Walter.ReeOrder.JT.Defs

public section

namespace CFSG.Walter.JT

open scoped MatrixGroups

@[expose] def SuzukiFourGroupTheorem : Prop :=
  ∀ (M : Type) [Group M] [Finite M],
    (∀ P : Sylow 2 M, IsKleinFour (P : Subgroup M)) →
    (∀ x y : M, orderOf x = 2 → orderOf y = 2 → IsConj x y) →
    (∀ x : M, orderOf x = 2 → IsMulCommutative (Subgroup.centralizer ({x} : Set M))) →
    (∀ P : Sylow 2 M, (P : Subgroup M).Normal) ∨
      ∃ L A : Subgroup M, Nonempty (L ≃* PSL(2, GaloisField 2 2)) ∧ IsMulCommutative A ∧
        Odd (Nat.card A) ∧ IsInternalDirectProduct L A ⊤

@[expose] def IsMetacyclic (P : Type*) [Group P] : Prop :=
  ∃ C : Subgroup P, ∃ _ : C.Normal, IsCyclic C ∧ IsCyclic (P ⧸ C)

@[expose] def HuppertMetacyclicTheorem : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p X,
    ¬ IsMulCommutative (P : Subgroup X) → IsMetacyclic (P : Subgroup X) →
      ∃ N : Subgroup X, ∃ _ : N.Normal, N ≠ ⊤ ∧ IsPGroup p (X ⧸ N)

end CFSG.Walter.JT
