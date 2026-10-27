module

public import CFSG.RankThree.GF2n.Tim81.Sec6.Defs

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec6

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n

variable {G : Type} [Group G] [Finite G]

@[expose] def Stmt60 (M V : Subgroup G) : Prop :=
  (∀ U ∈ sigmaSet M V, ∃ U' ∈ sigmaSet M V, IsL2Gen U U') ∧
    Nat.card V ^ 2 ∣ Nat.card (sigmaSet M V) ∧ ∀ U ∈ sigmaSet M V, V ≤ ⁅Pc M V, U⁆

@[expose] def Stmt61b (M V : Subgroup G) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ Nat.card ↥(Pc M V) = Nat.card V ^ (2 * n + 1) ∧
    ∀ g : G, conjSubgroup g V ∈ sigmaSet M V →
      Nat.card ↥(lOf M V g) = Nat.card V ^ (2 * n - 1) ∧
      Nat.card ↥(lOf M V g ⊓ Pc M V) = Nat.card V ^ 2 ∧
      Nat.card ↥(kOf V (hOf M V g)) = Nat.card V ^ (4 * n - 4)

end CFSG.RankThree.GF2n.Tim81.Sec6
