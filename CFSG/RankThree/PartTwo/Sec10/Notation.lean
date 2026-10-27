module

public import CFSG.RankThree.PartTwo.Sec9.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

structure Sec10Std (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (a : G) (R : Subgroup G) : Prop extends Sec9.Hyp91 G A c L a R where
  iso : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 3))

@[expose] def sec10D {G : Type*} [Group G] (c : G) (R L : Subgroup G) : Subgroup G :=
  Subgroup.zpowers c ⊔ (R ⊓ L)

end CFSG.RankThree.PartTwo.Sec10
