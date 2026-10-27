module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Inputs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def S16kEndF2Rank10 : Prop :=
  ∀ (Q : Type) [CommGroup Q] [Finite Q], (∀ x : Q, x ^ 2 = 1) → Nat.card Q = 2 ^ 10 →
    ∀ L : Subgroup (MulAut Q),
      (∀ B : Subgroup Q, (∀ l ∈ L, ∀ b ∈ B, l b ∈ B) → B = ⊥ ∨ B = ⊤) →
      (IsLn ↥L 5 1 ∨ IsSpor ↥L .M22) → Subgroup.centralizer (L : Set (MulAut Q)) = ⊥

@[expose] def S16kOutM22 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSpor X .M22 →
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) ∣ 2

@[expose] def IsE81A5 (X : Type) [Group X] : Prop :=
  ∃ (N : Subgroup X) (_ : N.Normal), IsElemAbelianOfRank 3 4 ↥N ∧ UC22.IsAlt (X ⧸ N) 5

@[expose] def IsE16A6 (X : Type) [Group X] : Prop :=
  ∃ (N : Subgroup X) (_ : N.Normal), IsElemAbelianOfRank 2 4 ↥N ∧ UC22.IsAlt (X ⧸ N) 6

@[expose] def S16kU43Table : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ H : Subgroup (MulAut W),
      (∃ S : Type, ∃ _ : Group S, CFSG.Blueprint.LieModel S .PSU 4 3 1 ∧ IsHat ↥H S) →
      rk ↥(⊤ : Subgroup W) = 12 → IsIrrOn H ⊤ ⊥ →
        ∀ w : W, w ≠ 1 →
          CFSG.Blueprint.LieModel ↥(ptCent H w) .PSU 4 2 1 ∨ IsE81A5 ↥(ptCent H w) ∨
            IsE16A6 ↥(ptCent H w)

@[expose] def S16kU43Noncyclic3 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ H : Subgroup (MulAut W),
      (∃ S : Type, ∃ _ : Group S, CFSG.Blueprint.LieModel S .PSU 4 3 1 ∧ IsHat ↥H S) →
      rk ↥(⊤ : Subgroup W) = 12 → IsIrrOn H ⊤ ⊥ →
        ∀ w : W, w ≠ 1 → ∃ B : Subgroup (MulAut W), B ≤ H ∧ IsPGroup 3 ↥B ∧ ¬ IsCyclic ↥B ∧
          ∀ b ∈ B, b w = w

structure S16kRowInputs : Prop where
  hI2 : S16kEndF2Rank10
  hOutM22 : S16kOutM22
  hSpC : RSp6SpinCent
  hSpF : RSp6SpinForm
  hSpSt : RSp6SpinStab
  hU43 : S16kU43Noncyclic3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
