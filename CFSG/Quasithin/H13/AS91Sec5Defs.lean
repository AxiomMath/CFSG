module

public import CFSG.Quasithin.H13.AS91Sec4DefsB
public import CFSG.Quasithin.H13.AS91Sec8Pt

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

abbrev G1 : Subgroup G := normalizer (c.E : Set G)

abbrev G2 : Subgroup G := normalizer (c.Z : Set G)

abbrev G3 (_c : Loc49 G z) : Subgroup G := H z

abbrev CZ : Subgroup G := centralizer (c.Z : Set G)

abbrev x0 : G ⧸ c.G1 := basePt c.G1

abbrev l0 : G ⧸ c.G2 := basePt c.G2

abbrev pi0 : G ⧸ c.G3 := basePt c.G3

abbrev Delta : SimpleGraph (G ⧸ c.G1) := colGraph c.G1 c.G2

abbrev ptsL : Set (G ⧸ c.G1) := objOf c.G1 c.G2 c.l0

abbrev plsL : Set (G ⧸ c.G3) := objOf c.G3 c.G2 c.l0

abbrev ptsP : Set (G ⧸ c.G1) := objOf c.G1 c.G3 c.pi0

abbrev lnsP : Set (G ⧸ c.G2) := objOf c.G2 c.G3 c.pi0

abbrev nbrP : Set (G ⧸ c.G1) := {a | a ∈ c.ptsP ∧ c.Delta.Adj c.x0 a}

abbrev farP : Set (G ⧸ c.G1) := {a | a ∈ c.ptsP ∧ a ≠ c.x0 ∧ ¬ c.Delta.Adj c.x0 a}

end Loc49

@[expose] def Stmt5_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
    Nat.card c.ptsL = 5 ∧ Nat.card c.plsL = 7 ∧
    (∀ g ∈ c.G2, (∀ p ∈ c.ptsL, g • p = p) ↔ g ∈ c.K) ∧
    (∀ g ∈ c.G2, (∀ q ∈ c.plsL, g • q = q) ↔ g ∈ c.CZ) ∧
    ∀ y ∈ c.ptsL, y ≠ c.x0 →
      (∃ Y : Subgroup G, Y ≤ c.CZ ⊓ c.G1 ∧ IsPGroup 3 Y ∧
        (∀ P : Subgroup G, P ≤ c.CZ ⊓ c.G1 → IsPGroup 3 P → Nat.card P ≤ Nat.card Y) ∧
        c.G1 ⊓ stabilizer G y = c.K ⊔ (c.CZ ⊓ c.G1 ⊓ normalizer (Y : Set G))) ∧
      pCoreOf 2 (c.G1 ⊓ stabilizer G y) = c.R ∧
      (∀ g ∈ c.G2, g • c.x0 = y → (c.E.map (MulAut.conj g).toMonoidHom) ⊓ c.E = c.Z) ∧
      (∀ g ∈ c.G2, g • c.x0 = y → c.G1.relIndex (c.E.map (MulAut.conj g).toMonoidHom) = 4)

@[expose] def Stmt5_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
    ∀ a b d : G ⧸ c.G1, c.Delta.Adj a b → c.Delta.Adj b d → c.Delta.Adj a d →
      ∃ p : G ⧸ c.G3, CInc c.G1 c.G3 a p ∧ CInc c.G1 c.G3 b p ∧ CInc c.G1 c.G3 d p

@[expose] def Stmt5_2u : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
    c.G1 ≤ (c.G1 ⊓ c.G2) ⊔ (c.G1 ⊓ c.G3) ∧ c.G3 ≤ (c.G3 ⊓ c.G1) ⊔ (c.G3 ⊓ c.G2)

@[expose] def Stmt5_3_1u : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
    ∀ a ∈ c.nbrP, ∀ b ∈ c.nbrP, ∃ g ∈ c.G1 ⊓ c.G3, g • a = b

end CFSG.Quasithin.H13.AS91
