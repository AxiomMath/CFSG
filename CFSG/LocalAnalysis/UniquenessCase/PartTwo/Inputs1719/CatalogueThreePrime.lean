module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def K_CatalogueThreePrimeSz : Prop :=
  ∀ (J : Type) [Group J] [Finite J], CFSG.Open.IsKGroup J →
    CFSG.Open.IsQuasisimple J → 3 ∉ piSet (⊤ : Subgroup J) →
      ∃ n : ℕ, IsSz (J ⧸ CFSG.pCore 2 J) n

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
