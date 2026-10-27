module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S29

public section

namespace CFSG.LocalAnalysis.UniquenessCase

open Subgroup CFSG.Open

namespace UC6

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

@[expose] def C631 : Prop := ⁅m.A ⊓ m.L, m.K⁆ ≤ m.U

end Mz614

end UC6

namespace UCK

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

@[expose] def K35c : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ N : Subgroup X, IsStronglyPEmbedded p N → 2 < CFSG.Open.pRank p (⊤ : Subgroup X) →
      CFSG.HallHigman.IsPSolvable p ↥N

end UCK

end CFSG.LocalAnalysis.UniquenessCase
