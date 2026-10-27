module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
public import CFSG.RankThree.PartTwo.Sec8.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec9

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo


structure Hyp91Small (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (a : G) (R : Subgroup G) : Prop extends Sec8.Hyp81 G A c L a where
  card_eq : Nat.card A = 27
  not_lTwoEight : ¬ Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃*
    CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 3))
  not_slThreePiEight : ¬ Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) 8
  isSylowOf : CFSG.ABGLocalTools.IsSylowOf 3 R (Subgroup.normalizer (Subgroup.zpowers c : Set G))
  isSylowOf_inf : CFSG.ABGLocalTools.IsSylowOf 3 (R ⊓ Subgroup.normalizer (A : Set G))
    (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (A : Set G))
  not_mem_partTwoT_or_mem_partTwoS : A ∉ partTwoT G ∨ A ∈ partTwoS G

@[expose] def Hyp91SmallNever : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), ¬ Hyp91Small G A c L a R

end CFSG.RankThree.PartTwo.Sec9
