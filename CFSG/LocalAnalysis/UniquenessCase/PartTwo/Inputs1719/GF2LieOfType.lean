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

@[expose] def GF2PermType (t : StatedLieTag) (m : ℕ) : Prop :=
  ¬ (t = .PSL ∧ m ≤ 3) ∧ t ≠ .trialityD4 ∧ t ≠ .Tits

@[expose] def K_GF2_permutabilityOfType : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), K.Normal →
    Odd (Nat.card (Subgroup.center ↥K)) →
    ∀ (t : StatedLieTag) (m : ℕ), StatedLieAdmissible t m 2 1 → GF2PermType t m →
      LieModel (↥K ⧸ Subgroup.center ↥K) t m 2 1 →
      ∀ S : Subgroup Y, CFSG.Quasithin.IsSylowIn 2 S ⊤ →
        ∃ E : Subgroup Y,
          E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧ ¬ IsCyclic ↥E ∧
            Permutes E S

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
