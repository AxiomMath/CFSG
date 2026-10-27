module

public import CFSG.RankThree.PartTwo.Sec11.LaterSteps

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Sylow1129 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g a' : G), Sec11Data G A c L a R Y d x s r g →
      Subgroup.zpowers s = Subgroup.zpowers c →
      Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s} → orderOf x = 9 →
      a' ∈ A → a' ∉ Subgroup.closure {c, d} →
      ⁅sec11P R g, sec11P R g⁆ = Subgroup.closure {a', d} → YNotField c L a' →
        CFSG.ABGLocalTools.IsSylowOf 3 (sec11P R g ⊓ Subgroup.centralizer {a'})
          (Subgroup.centralizer {a'})

end CFSG.RankThree.PartTwo.Sec11
