module

public import CFSG.Foundations.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

variable {G : Type} [Group G]

@[expose] noncomputable def fstarPreimage (p : ℕ) (H : Subgroup G) : Subgroup G :=
  ((CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore p ↥H)).comap
    (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))).map H.subtype

@[expose] noncomputable def layerLift (p : ℕ) (H : Subgroup G) : Subgroup G :=
  (⨅ n : ℕ, derivedSeries ↥(fstarPreimage p H) n).map (fstarPreimage p H).subtype

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
