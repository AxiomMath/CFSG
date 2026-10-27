module

public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UCK (fixV ExtraspecialExpP)

@[expose] def thompsonJ {G : Type} [Group G] (X : Subgroup G) : Subgroup G :=
  CFSG.inSubgroup (fun K _ => CFSG.elemThompson K 2) X

@[expose] def omegaOneZJ {G : Type} [Group G] (X : Subgroup G) : Subgroup G :=
  CFSG.inSubgroup (fun K _ => CFSG.elemThompsonCenterTorsion K 2) X

@[expose] def InX390 (L : Type) [Group L] [Finite L] : Prop :=
  CFSG.RankThree.PartOne.InClassX L ∧ ∀ u ∈ CFSG.RankThree.PartOne.shortU L, u ^ 2 = 1

@[expose] def InOmega {G : Type} [Group G] [Finite G] (T H E Z : Subgroup G) : Prop :=
  H = thompsonJ H ∧
  (Fstar H = CFSG.Open.pCoreOf 2 H ∧ (∃ n : ℕ, IsL2 (Bar2 H) n) ∧
    ¬ InX390 ↥(CFSG.RankThree.PartOne.oResidualTwo ↥H)) ∧
  E = omegaOneZJ (CFSG.Open.pCoreOf 2 H) ∧
  ((∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S H ∧ T = thompsonJ S ∧
      ¬ CFSG.RankThree.PartOne.omegaOneCenterIn S ≤ (Subgroup.center ↥H).map H.subtype) ∧
    Z = ⁅T, E⁆)

@[expose] def hyperplanes {G : Type} [Group G] (q : ℕ) (A : Subgroup G) : Set (Subgroup G) :=
  {D | D ≤ A ∧ D.relIndex A = q}

@[expose] def K331 : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L → CFSG.Open.IsCatalogGroup L →
    CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2 →
    ∀ T : Subgroup L, CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ →
    ∀ K : Subgroup L, IsAlt (Bar2 K) 8 → T ≤ Subgroup.normalizer (K : Set L) →
      K = ⊤ ∨ LieModel L .PSL 5 2 1 ∨ IsSpor L .M24 ∨ IsSpor L .J4

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
