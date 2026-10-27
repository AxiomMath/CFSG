module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326P1Loc
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326CompDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

@[expose] def K334Cover : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L →
    CFSG.Open.IsCatalogGroup (L ⧸ Subgroup.center L) → IsPGroup 3 (Subgroup.center L) →
    (CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2 ∨ CFSG.Open.pRank 3 (⊤ : Subgroup L) = 3) →
    Subgroup.center L ≠ ⊥ → IsSL3pi L ∨ ExcludedCover L

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
