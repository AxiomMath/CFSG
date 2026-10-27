module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
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
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def KYForm (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y) : Prop :=
  K.Normal ∧ CFSG.Open.IsQuasisimple ↥K ∧ Odd (Nat.card (Subgroup.center ↥K)) ∧
    Subgroup.centralizer (K : Set Y) = (Subgroup.center ↥K).map K.subtype ∧
    (∃ a : ℕ, K.index = 2 ^ a) ∧ CFSG.Quasithin.IsSylowIn 2 S ⊤

@[expose] def K_A7Permuting : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y), KYForm Y K S →
    Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 7)) →
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥E ∧ Permutes E S

@[expose] def K_U33Local : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y), KYForm Y K S →
    LieModel ↥K .PSU 3 3 1 →
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ E ≤ (Subgroup.center ↥K).map K.subtype ∧ Permutes E S

@[expose] def K_L33Local : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y), KYForm Y K S →
    LieModel ↥K .PSL 3 3 1 →
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ E ≤ (Subgroup.center ↥K).map K.subtype ∧ Permutes E S

@[expose] def K_U33SThreePair : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y), KYForm Y K S →
    LieModel ↥K .PSU 3 3 1 →
    ∃ P₁ P₂ : Subgroup Y, S ≤ P₁ ∧ S ≤ P₂ ∧ P₁ ⊔ P₂ = ⊤ ∧
      Nonempty (Bar2 P₁ ≃* Equiv.Perm (Fin 3)) ∧
        Nonempty (Bar2 P₂ ≃* Equiv.Perm (Fin 3))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
