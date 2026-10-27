module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Opp IsSpor)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

@[expose] def K35w : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ M : Subgroup G, IsStronglyPEmbedded p M → 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) →
    CFSG.pPrimeCore p G = ⊥ →
      CFSG.HallHigman.IsPSolvable p ↥M ∨
      Nonempty (↥(Opp p (⊤ : Subgroup G)) ≃* alternatingGroup (Fin (2 * p))) ∨
      (p = 5 ∧ IsSpor ↥(Opp p (⊤ : Subgroup G)) .Fi22)

end CFSG.LocalAnalysis.UniquenessCase.UCK
