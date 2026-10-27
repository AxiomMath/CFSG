module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.F1Models
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def K_2F4Parabolic : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), CFSG.Quasithin.Is2F4 n X → Odd n → 1 < n →
    (2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) ∧ Nat.card (Outer X) = n) ∧
      ∀ S : Subgroup X, IsSylowTwoOf S ⊤ →
        ∃ P₁ P₂ : Subgroup X,
          S ≤ P₁ ∧ S ≤ P₂ ∧ P₁ < ⊤ ∧ P₂ < ⊤ ∧ P₁ ≠ P₂ ∧
          (∃ Y : Subgroup X, Y ≤ P₁ ∧ (Y.subgroupOf P₁).Normal ∧ IsSz (Bar2 Y) n ∧
            Odd (Nat.card (Outer (Bar2 Y))) ∧ S ≤ normalizer (Y : Set X)) ∧
          (∃ Y : Subgroup X, Y ≤ P₂ ∧ (Y.subgroupOf P₂).Normal ∧ IsL2 (Bar2 Y) n ∧
            Odd (Nat.card (Outer (Bar2 Y))) ∧ S ≤ normalizer (Y : Set X))

@[expose] def K_TitsParabolic : Prop :=
  ∀ (X : Type) [Group X] [Finite X], LieModel X .Tits 0 2 1 →
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 ∧
      ∀ S : Subgroup X, IsSylowTwoOf S ⊤ →
        ∃ P₁ P₂ : Subgroup X,
          S ≤ P₁ ∧ S ≤ P₂ ∧ P₁ < ⊤ ∧ P₂ < ⊤ ∧ P₁ ≠ P₂ ∧
          Nat.card ↥P₁ = 6144 ∧ Nat.card ↥P₂ = 10240 ∧
          Group.IsSolvable ↥P₁ ∧ Group.IsSolvable ↥P₂

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
