module

public import CFSG.RankThree.PartTwo.Sec17.Item17TailData

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

@[expose] def Item1724N : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (w : G) (Q : Subgroup G), Sec17W G A c L Y₀ Y₁ S p P w Q →
      (∀ Q₁ ∈ scriptQPiStar A (lB A) ⊤ (piOf p), ∀ Q₂ ∈ scriptQPiStar A (lB A) ⊤ (piOf p),
          IsConjIn (xA A) Q₁ Q₂) ∧
        Q ⊓ Subgroup.normalizer (Y₀ : Set G) = ⊥

end CFSG.RankThree.PartTwo.Sec17
