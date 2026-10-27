module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.Sporadic.Schreier

open CFSG.ComponentClassification.OuterAutomorphisms

theorem outer_card_le_of_equiv {G H : Type*} [Group G] [Group H] {k : ℕ}
    (hH : Nat.card (Outer H) ≤ k) (e : G ≃* H) : Nat.card (Outer G) ≤ k := by
  rw [Nat.card_congr (equivalence e).toEquiv]
  exact hH

end CFSG.Sporadic.Schreier
