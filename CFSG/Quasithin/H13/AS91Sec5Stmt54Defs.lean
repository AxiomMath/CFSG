module

public import CFSG.Quasithin.H13.AS91Sec5More

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction

@[expose] def Stmt5_4_34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
    ∀ y ∈ c.ptsL, y ≠ c.x0 →
      (∀ k ∈ c.delta 1, {a | a ∈ objOf c.G1 c.G2 k ∧ c.Delta.Adj y a}.ncard = 3) ∧
      (∀ k ∈ c.delta 2, ∀ a ∈ objOf c.G1 c.G2 k, c.Delta.Adj y a)

@[expose] def Stmt5_4_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
    ∀ y ∈ c.ptsL, y ≠ c.x0 →
      ∀ i : Fin 5, 1 < i → ∀ k ∈ c.delta i, ∀ p ∈ objOf c.G1 c.G2 k, ∀ q ∈ objOf c.G1 c.G2 k,
        p ≠ c.x0 → q ≠ c.x0 → ∃ e ∈ c.E ⊓ stabilizer G y, e • p = q

end CFSG.Quasithin.H13.AS91
