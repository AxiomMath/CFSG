module

public import CFSG.Quasithin.H13.AS91Sec5Defs
public import CFSG.Quasithin.H13.AS91Sec1Defs

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction
open scoped Pointwise

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

abbrev lnsX : Set (G ⧸ c.G2) := objOf c.G2 c.G1 c.x0

@[expose] def deltaSize : Fin 5 → ℕ := ![1, 42, 56, 1008, 2688]

@[expose] def delta (i : Fin 5) : Set (G ⧸ c.G2) :=
  {m | m ∈ c.lnsX ∧ (MulAction.orbit ↥(c.G1 ⊓ c.G2) m).ncard = deltaSize i}

@[expose] def deltaAt (i : Fin 5) (a : G ⧸ c.G1) (m : G ⧸ c.G2) : Set (G ⧸ c.G2) :=
  {n | ∃ g : G, g • c.x0 = a ∧ g • c.l0 = m ∧ g⁻¹ • n ∈ c.delta i}

end Loc49

@[expose] def Stmt5_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
    ∀ y ∈ c.ptsL, y ≠ c.x0 →
      (∀ m ∈ c.lnsX, ∃ i, m ∈ c.delta i) ∧
      (∀ i, ∃ m ∈ c.delta i, ∀ n ∈ c.delta i, ∃ g ∈ c.G1 ⊓ c.G2, g • m = n) ∧
      (c.delta 0 = {c.l0}) ∧
      ((c.delta 0 ∪ c.delta 1 ∪ c.delta 2) =
        {m | m ∈ c.lnsX ∧ ∃ p, CInc c.G2 c.G3 m p ∧ CInc c.G2 c.G3 c.l0 p}) ∧
      ((c.delta 1).ncard = 42 ∧ ∀ k ∈ c.delta 1,
        {a | a ∈ objOf c.G1 c.G2 k ∧ c.Delta.Adj y a}.ncard = 3) ∧
      ((c.delta 2).ncard = 56 ∧ ∀ k ∈ c.delta 2, ∀ a ∈ objOf c.G1 c.G2 k, c.Delta.Adj y a) ∧
      ((c.delta 3).ncard = 1008 ∧ (c.delta 4).ncard = 2688) ∧
      (∀ i : Fin 5, 1 < i → ∀ k ∈ c.delta i, ∀ p ∈ objOf c.G1 c.G2 k, ∀ q ∈ objOf c.G1 c.G2 k,
        p ≠ c.x0 → q ≠ c.x0 → ∃ e ∈ c.E ⊓ stabilizer G y, e • p = q)

@[expose] def Stmt5_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
    ∀ a b d : G ⧸ c.G1, c.Delta.Adj a b → c.Delta.Adj b d → c.Delta.Adj a d →
      (∀ m n : G ⧸ c.G2, CInc c.G1 c.G2 a m → CInc c.G1 c.G2 b m →
        CInc c.G1 c.G2 a n → CInc c.G1 c.G2 d n → ∃ i : Fin 5, i ≤ 2 ∧ n ∈ c.deltaAt i a m) ∧
      ((∃ g : G, g • a = b ∧ g • b = a ∧ g • d = d) ∧ (∃ g : G, g • a = d ∧ g • d = a ∧ g • b = b) ∧
        ∃ g : G, g • b = d ∧ g • d = b ∧ g • a = a) ∧
      (∀ (m n n' : G ⧸ c.G2) (i : Fin 5), CInc c.G1 c.G2 a m → CInc c.G1 c.G2 b m →
        CInc c.G1 c.G2 a n → CInc c.G1 c.G2 d n → CInc c.G1 c.G2 b n' → CInc c.G1 c.G2 d n' →
        n ∈ c.deltaAt i a m → n' ∈ c.deltaAt i b m)

@[expose] def Stmt5_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
    ∀ y : G ⧸ c.G1, Dist2 c.Delta c.x0 y → (∃ p, CInc c.G1 c.G3 c.x0 p ∧ CInc c.G1 c.G3 y p) →
      y ∈ c.ptsP → ∀ u : G ⧸ c.G1, c.Delta.Adj c.x0 u → c.Delta.Adj y u → u ∈ c.ptsP

end CFSG.Quasithin.H13.AS91
