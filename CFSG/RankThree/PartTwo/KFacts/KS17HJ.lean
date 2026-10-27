module

public import CFSG.RankThree.PartTwo.Sec13.Notation

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13

@[expose] def KS17HJConjugacy : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L →
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ a : G, Subgroup.zpowers a ∈ omegaA A →
      ∀ B ∈ partTwoE G, B ≤ Subgroup.centralizer ({a} : Set G) →
        ∃ x ∈ Subgroup.centralizer ({a} : Set G), B = A.map (MulAut.conj x).toMonoidHom

end CFSG.RankThree.PartTwo.KFacts
