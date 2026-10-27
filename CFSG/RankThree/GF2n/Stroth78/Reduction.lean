module

public import CFSG.RankThree.GF2n.Tim79aCitedInvol

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a
open CFSG.LargeExtraspecial.Timmesfeld (Qa)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

@[expose] def Stroth78Hyperplane (z : G) : Prop :=
  ∃ R : Subgroup G, R ≤ centerIn (Qa z) ∧ Nat.card (centerIn (Qa z)) = 2 * Nat.card R ∧
    ¬ Subgroup.centralizer (R : Set G) ≤
      (Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer (R : Set G)) ⊔
        inSubgroup (pPrimeCore 2) (Subgroup.centralizer (R : Set G))

@[expose] def Stroth78Assumption212 (z : G) : Prop := ¬ Stroth78Hyperplane z

end CFSG.RankThree.GF2n.Stroth78
