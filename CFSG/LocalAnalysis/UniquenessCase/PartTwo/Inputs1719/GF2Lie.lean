module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Open.StatedDefs
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

@[expose] def K_GF2_permutability : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y),
    K.Normal →
    CFSG.Open.IsQuasisimple ↥K →
    Odd (Nat.card (Subgroup.center ↥K)) →
    (∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m : ℕ),
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t m 2 1 ∧
        LieModel (↥K ⧸ Subgroup.center ↥K) t m 2 1) →
    (2 < CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ∨
      LieModel (↥K ⧸ Subgroup.center ↥K) .PSL 5 2 1) →
    Subgroup.centralizer (K : Set Y) = (Subgroup.center ↥K).map K.subtype →
    (∃ n : ℕ, K.index = 2 ^ n) →
    ∀ S : Subgroup Y, CFSG.Quasithin.IsSylowIn 2 S ⊤ →
      ∃ E : Subgroup Y,
        E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧ ¬ IsCyclic ↥E ∧
          CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes E S

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
