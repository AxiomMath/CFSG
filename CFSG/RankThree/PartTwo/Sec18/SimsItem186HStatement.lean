module

public import CFSG.RankThree.PartTwo.Sec18.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

@[expose] def Item182Alt1At {G : Type} [Group G] (H : Subgroup G) : Prop :=
  ∀ X : Subgroup G, H ≤ X → X ≠ ⊤ →
    ∃ K ∈ oTwoComponentsIn X, K = inSubgroup perfectResidual H ⊔ CFSG.Open.pCoreOf 2 K

@[expose] def Item186H : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Sec18H G A M H c →
    Hyp187 A M H c →
      CFSG.generalizedFitting H = CFSG.pCore 2 H ∧
      (CFSG.Open.pCoreOf 2 (H ⊓ M) ∈ maxInvariantPiSubgroups ⊤ A (piOf 2) ∧
        Subgroup.normalizer (CFSG.Open.pCoreOf 2 (H ⊓ M) : Set G) ≤
          Subgroup.normalizer (inSubgroup perfectResidual H : Set G)) ∧
      scriptN (H : Set G) = {Subgroup.normalizer (inSubgroup perfectResidual H : Set G)} ∧
        IsMaximalTwoLocal (Subgroup.normalizer (inSubgroup perfectResidual H : Set G))

end CFSG.RankThree.PartTwo.Sec18
