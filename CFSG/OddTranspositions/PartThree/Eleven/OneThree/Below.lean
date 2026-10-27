module

public import CFSG.OddTranspositions.PartThree.Statements

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

@[expose] def Theorem11_3Below (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D), Nat.card G < n →
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) →
    ¬ (∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) →
    (CFSG.solvableRadical (Halpha D hC.alpha)).map
        (QuotientGroup.mk' (CFSG.pCore 2 (Halpha D hC.alpha))) =
      Subgroup.center (Halpha D hC.alpha ⧸ CFSG.pCore 2 (Halpha D hC.alpha))

theorem theorem11_3_of_forall_below (h : ∀ n, Theorem11_3Below n) : Theorem11_3 :=
  fun G _ _ D hC => h (Nat.card G + 1) G D hC (Nat.lt_succ_self _)

end CFSG.OddTranspositions.PartThree
