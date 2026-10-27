module

public import CFSG.RankThree.PartTwo.Sec11.Final

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

@[expose] def Sylow11Case {G : Type*} [Group G] (c a : G) (R Y : Subgroup G) (d x s r g e : G)
    (Y' : Subgroup G) : Prop :=
  (e = a ∧ Y' = Y ∧ 9 < orderOf x ∧ orderOf g = 3 ∧
      (Subgroup.zpowers s ≠ Subgroup.zpowers c ∨
        Subgroup.closure ({r, s} : Set G) ≠ Subgroup.closure {a, s})) ∨
    (Subgroup.zpowers s = Subgroup.zpowers c ∧
      Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s} ∧ orderOf x = 9 ∧
      ⁅sec11P R g, sec11P R g⁆ = Subgroup.closure {e, d})

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g e : G} {Y' : Subgroup G}

end CFSG.RankThree.PartTwo.Sec11
