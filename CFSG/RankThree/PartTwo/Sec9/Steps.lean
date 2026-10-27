module

public import CFSG.RankThree.PartTwo.Sec9.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec9

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item95 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G) (n : ℕ), Hyp92 G A c L a R n →
      ∀ g : G, g * c * g⁻¹ ∈ R →
        KFacts.InducesStdKind L (g * c * g⁻¹) .inner ∨
          KFacts.InducesStdKind L (g * c * g⁻¹) .diagonal

end CFSG.RankThree.PartTwo.Sec9
