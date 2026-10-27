module

public import CFSG.CGT.PushingUp.Defs
public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData

public section

namespace CFSG.RankThree.PartOne.SolD3

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.Timmesfeld75
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AschbacherKnownGroup
open CFSG.Assembly (InCatalog KProper pCoreOf)
open CFSG.Open (IsElemAbelian)

@[expose] def WCBlockCentralizerThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → CFSG.Assembly.IsCharTwoType G →
    ∀ (R X : Subgroup G), IsElemAbelian 2 R → 4 ≤ Nat.card R → IsTI R →
      IsMaximalTwoLocal (Subgroup.normalizer (R : Set G)) →
      WeaklyClosedIn R (Subgroup.normalizer (R : Set G)) →
      CFSG.maximalTwoLocalsContaining (X : Set G) = {Subgroup.normalizer (R : Set G)} →
      X ≤ Subgroup.normalizer (R : Set G) →
      (X.subgroupOf (Subgroup.normalizer (R : Set G))).Normal →
      IsShortGroup ↥X → IsNaturalAltModule ↥X 1 → X ≤ Subgroup.centralizer (R : Set G) → False

@[expose] def SzU3SylowIndecomposable : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    ((∃ s : ℕ, Odd s ∧ 3 ≤ s ∧ CFSG.Blueprint.LieModel G .twistedB2 0 2 s) ∨
      (∃ s : ℕ, 2 ≤ s ∧ StatedClassicalModel G .PSU 3 2 s)) →
    ∀ (Q : Sylow 2 G) (W R : Subgroup G), W ≠ ⊥ → W ≤ (Q : Subgroup G) →
      R ≤ (Q : Subgroup G) → (∀ w ∈ W, ∀ q ∈ (Q : Subgroup G), w * q = q * w) →
      W ⊓ R = ⊥ → (∀ q ∈ (Q : Subgroup G), ∃ w ∈ W, ∃ r ∈ R, q = w * r) → False

end CFSG.RankThree.PartOne.SolD3
