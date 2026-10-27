module

public import CFSG.RankThree.PartTwo.Sec9.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def sec11K {G : Type*} [Group G] (L : Subgroup G) (a : G) : Subgroup G :=
  inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G))

structure Sec11Std (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (a : G) (R Y : Subgroup G) : Prop extends Sec9.Hyp91 G A c L a R where
  isList1016 : Sec9.IsList1016 (L ⧸ aschbacherSolvableCore 3 L)
  mem_thetaComponentsAt_Y : Y ∈ thetaComponentsAt 3 a
  sec11K_le : sec11K L a ≤ Y

end CFSG.RankThree.PartTwo.Sec11
