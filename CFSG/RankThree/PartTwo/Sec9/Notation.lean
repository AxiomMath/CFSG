module

public import CFSG.RankThree.PartTwo.Sec8.Notation
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec9

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

structure Hyp91 (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (a : G) (R : Subgroup G) : Prop extends Sec8.Hyp81 G A c L a where
  card_eq : Nat.card A = 27
  invTwo_or_commutator : (Sec8.InvTwoBarNontrivial A L ∨
    ∃ A' : Subgroup G, A' ≤ A ∧ Nat.card A = 3 * Nat.card A' ∧ c ∈ A' ∧
      ¬ ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (A' : Set G)), A⁆ ≤
        Sec4.thetaQuotCentralizer L) ∨
    (¬ Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃*
        CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 3)) ∧
      ¬ Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) 8)
  isSylowOf : CFSG.ABGLocalTools.IsSylowOf 3 R (Subgroup.normalizer (Subgroup.zpowers c : Set G))
  isSylowOf_inf : CFSG.ABGLocalTools.IsSylowOf 3 (R ⊓ Subgroup.normalizer (A : Set G))
    (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (A : Set G))
  not_mem_partTwoT_or_mem_partTwoS : A ∉ partTwoT G ∨ A ∈ partTwoS G

structure Hyp92 (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (a : G) (R : Subgroup G) (n : ℕ) : Prop extends Hyp91 G A c L a R where
  isSLThreePiAt : Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * n))

end CFSG.RankThree.PartTwo.Sec9
