module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairActionQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.ProperPairModel

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type} [Group G]

@[expose] def baseOrbit (H K : Subgroup G) : Set (rightCosetSpace H) :=
  {ω | ∃ x ∈ K, rightCosetMk H x = ω}

@[expose] def rightFixedSet (H : Subgroup G) (u : G) : Set (rightCosetSpace H) :=
  {ω | rightCosetTranslate H ω u = ω}

@[expose] def PairInvolutionCentralizesConclusion (H : Subgroup G) (z : G)
    (beta : rightCosetSpace H) (t u : G) : Prop :=
  minimalLocalFailurePairActionPointHull H z ≤ Subgroup.centralizer {u} ∧
    minimalLocalFailureProperPairHull H z beta t ≤ Subgroup.centralizer {u} ∧
    ∃ i : ℕ, (i = 1 ∨ i = 2 ∨ i = 3) ∧
      Nat.card (rightFixedSet H u) = Nat.card (minimalLocalFailurePairActionPointHull H z) ^ i + 1 ∧
      Nat.card (rightCosetSpace H) =
        (Nat.card (minimalLocalFailurePairActionPointHull H z) ^ i + 1) *
          (Nat.card (minimalLocalFailurePairActionPointHull H z) ^ i *
            (Nat.card (minimalLocalFailurePairActionPointHull H z) - 1) + 1)

@[expose] def UnitaryFixedModelExcludedConclusion (H : Subgroup G) (z u : G) : Prop :=
  ∃ i : ℕ, (i = 1 ∨ i = 2) ∧
    Nat.card (rightFixedSet H u) = Nat.card (minimalLocalFailurePairActionPointHull H z) ^ i + 1 ∧
    Nat.card (rightCosetSpace H) =
      (Nat.card (minimalLocalFailurePairActionPointHull H z) ^ i + 1) *
        (Nat.card (minimalLocalFailurePairActionPointHull H z) ^ i *
          (Nat.card (minimalLocalFailurePairActionPointHull H z) - 1) + 1)

@[expose] def RegularComplementConclusion (H : Subgroup G) (z : G)
    (beta : rightCosetSpace H) (t u : G) : Prop :=
  Subgroup.closure (involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G)) =
      minimalLocalFailureProperPairHull H z beta t ∧
    rightFixedSet H u = baseOrbit H (minimalLocalFailureProperPairHull H z beta t) ∧
    ((∃ (k : Type) (_ : Field k) (_ : Finite k),
        Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
        Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* PSL2MatrixGroup k)) ∧
        Nat.card (rightFixedSet H u) = Nat.card (minimalLocalFailurePairActionPointHull H z) + 1 ∨
      (∃ (m : ℕ) (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (2 * m + 1) ∧
        Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
        Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* CFSG.Blueprint.suzukiGroup m k)) ∧
        Nat.card (rightFixedSet H u) =
          Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 2 + 1) ∧
    (rightFixedSet H u)ᶜ.Nonempty ∧
    (∀ ω ∈ (rightFixedSet H u)ᶜ, ∀ x ∈ minimalLocalFailureProperPairHull H z beta t,
      rightCosetTranslate H ω x ∈ (rightFixedSet H u)ᶜ) ∧
    Nat.card ↥(rightFixedSet H u)ᶜ = Nat.card (minimalLocalFailureProperPairHull H z beta t) ∧
    (∀ ω ∈ (rightFixedSet H u)ᶜ, ∀ ω' ∈ (rightFixedSet H u)ᶜ,
      ∃! x : minimalLocalFailureProperPairHull H z beta t, rightCosetTranslate H ω x = ω') ∧
    (∀ c ∈ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G),
      ∀ ω ∈ rightFixedSet H u, rightCosetTranslate H ω c = ω) ∧
    (∀ c ∈ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G),
      (∀ ω ∈ (rightFixedSet H u)ᶜ, rightCosetTranslate H ω c = ω) → c = 1) ∧
    ∃ f : Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G) →*
        minimalLocalFailureProperPairHull H z beta t, Function.Injective f

end CFSG.ShultStronglyClosedTI.ProperPairModel
