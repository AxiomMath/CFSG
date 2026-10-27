module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Open.StatedDefs
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

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def KSporadicThreeRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : TauCeti.SporadicName), IsSpor X s →
    (s = .J1 ↔ pRank 3 (⊤ : Subgroup X) = 1) ∧
      ((s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J2 ∨
          s = .HS ∨ s = .He ∨ s = .Ru ∨ s = .J4) ↔ pRank 3 (⊤ : Subgroup X) = 2)

@[expose] def KU34Data : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsU3 X 2 →
    Nat.card X = 2 ^ 6 * 3 * 5 ^ 2 * 13 ∧
      pRank 2 (⊤ : Subgroup X) = 2 ∧ pRank 3 (⊤ : Subgroup X) = 1 ∧
        pRank 5 (⊤ : Subgroup X) = 2 ∧ pRank 13 (⊤ : Subgroup X) = 1

@[expose] def KOmega6MinusU4 : Prop :=
  ∀ (X : Type) [Group X] (n : ℕ) (K : Type) [Field K] [Finite K] (b c : K),
    Nat.card K = 2 ^ n →
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
        Nonempty (X ≃* StatedProj (StatedOmega (StatedQuadMinus 3 K b c))) →
          LieModel X .PSU 4 2 n

@[expose] def K_U3FourPowThreeRankOne : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 1 ≤ n → IsU3 X (2 * n) →
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
