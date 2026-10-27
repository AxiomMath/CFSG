module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
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

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def TorusFacts (G : Type) [Group G] [Finite G] (L E : Subgroup G) (n : ℕ) : Prop :=
  ∀ B₀ : Subgroup G, F08.NotationB8103 L E n B₀ →
    ∃ B₁ : Subgroup G, B₁ ≤ F08.KOf8103 L B₀ ∧ F08.NotationB8103 L E n B₁ ∧ B₁ ≠ B₀ ∧
      (∀ Y : Subgroup G, F08.NotationB8103 L E n Y → Y = B₀ ∨ Y = B₁) ∧
      ∀ p : ℕ, p.Prime → p ∣ 2 ^ n + 1 →
        (∃ D₀ : Subgroup G, D₀ ≤ F08.KOf8103 L B₀ ∧ Nat.card D₀ = p ∧
          D₀ ≤ centralizer ((L ⊓ centralizer (E : Set G) : Subgroup G) : Set G)) ∧
        2 ≤ Open.pRank p (F08.KOf8103 L B₀ ⊔ F08.KOf8103 L B₁)

@[expose] def TorusAt (G : Type) [Group G] [Finite G] (L : Subgroup G) (n : ℕ) : Prop :=
  ∀ E : Subgroup G, E ≤ L → IsElemAbelian 3 E → Nat.card E = 9 → TorusFacts G L E n

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105
