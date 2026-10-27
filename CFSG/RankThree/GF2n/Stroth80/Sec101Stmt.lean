module

public import CFSG.RankThree.GF2n.Stroth80.Sec101Defs
public import CFSG.LargeExtraspecial.S111SHCor3

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement


@[expose] def Stroth101EndStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ), Sec10Hyp hc n → (∀ t : G, ¬ Good101 M Q Z B t) →
    ∀ X : Subgroup G, IsMaxClique101 M Q Z B X → IsSaturated101 M Q Z B X → B ≤ X →
    ∀ S : Sylow 2 (↥M ⧸ Q.subgroupOf M),
      (S : Subgroup (↥M ⧸ Q.subgroupOf M)) ≤
        Subgroup.normalizer ((bar M Q (LB M Q B) : Subgroup (↥M ⧸ Q.subgroupOf M)) :
          Set (↥M ⧸ Q.subgroupOf M)) →
    ∀ t ∈ bar M Q (LB M Q B), t ≠ 1 → t ∈ (S : Subgroup (↥M ⧸ Q.subgroupOf M)) →
      (∀ x ∈ (S : Subgroup (↥M ⧸ Q.subgroupOf M)), x * t = t * x) →
      t ∈ inSubgroup (pCore 2) (bar M Q (M ⊓ Subgroup.normalizer (X : Set G))) →
      IsMulCommutative ↥(CFSG.LargeExtraspecial.S11.wcl t) → False

end CFSG.RankThree.GF2n.Stroth80
