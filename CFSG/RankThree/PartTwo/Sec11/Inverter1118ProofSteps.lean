module

public import CFSG.RankThree.PartTwo.Sec11.LaterSteps

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Step1118S : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Big G A c L a R Y d x s r g →
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G) →
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers d : Set G) →
      Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s} →
      (∀ (K : Subgroup (sec11P R g)) [K.Normal], IsEmpty (sec11P R g ⧸ K ≃* W33)) →
        s ∉ ⁅sec11P R g, sec11P R g⁆ ⊔ Subgroup.closure {x ^ 3, s ^ 3}

end CFSG.RankThree.PartTwo.Sec11
