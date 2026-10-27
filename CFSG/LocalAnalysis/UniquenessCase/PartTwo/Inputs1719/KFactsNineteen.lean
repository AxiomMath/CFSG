module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmTwoDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

@[expose] def K_CatalogModels : Prop :=
  (∀ (X : Type) [Group X] (r : ℕ),
      CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64IsLie r X →
        CFSG.LocalAnalysis.UniquenessCase.UC22.IsChev X r) ∧
    (∀ (X : Type) [Group X] (s : TauCeti.SporadicName),
      CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64IsSpor s X →
        CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor X s)

@[expose] def K_TitsOddPrimes : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    CFSG.LocalAnalysis.UniquenessCase.UC22.F10.IsTits10 ↥(CFSG.Open.genFittingFStar X) →
    Subgroup.centralizer (CFSG.Open.genFittingFStar X : Set X) = ⊥ →
    ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ Nat.card X → q = 3 ∨ q = 5 ∨ q = 13

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
