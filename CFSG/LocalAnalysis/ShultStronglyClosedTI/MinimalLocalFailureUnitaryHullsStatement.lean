module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureChainInterface
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureOvergroupHullUnique

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.ProperPairModel

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.OvergroupHull

variable {G : Type} [Group G]

@[expose] def UnitaryFixedHullsConclusion (H : Subgroup G) (z : G)
    (beta : rightCosetSpace H) (t u : G) : Prop :=
  let B := pairPointStabilizer H beta
  let K := minimalLocalFailureProperPairHull H z beta t
  let q := Nat.card (minimalLocalFailurePairActionPointHull H z)
  let D := involutionPointClass z
  let Lu := Subgroup.closure (D ∩ (Subgroup.centralizer ({u} : Set G) : Set G))
  (∃ (k : Type) (_ : Field k) (_ : Finite k),
      Nat.card k = q ∧ Nonempty (K ≃* PSL2MatrixGroup k)) ∧
    IsUnitaryScalarQuotient q Lu ∧ baseOrbit H Lu = rightFixedSet H u ∧
    CFSG.oddCore Lu ≤ Subgroup.center Lu ∧ Nat.card (CFSG.oddCore Lu) ∣ Nat.gcd 3 (q + 1) ∧
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ q + 1 ∧
      ∃ A A₀ : Subgroup G, A ≤ B ⊓ Lu ∧ IsCyclic A ∧ IsPGroup p A ∧ A ≠ ⊥ ∧
        A ≤ Subgroup.centralizer (K : Set G) ∧ A ≤ Subgroup.centralizer ({u} : Set G) ∧
        A₀ ≤ B ⊓ Lu ∧ IsCyclic A₀ ∧ Odd (Nat.card A₀) ∧ A ≤ A₀ ∧
        (∃ e : K × A₀ ≃* (Lu ⊓ Subgroup.centralizer (A : Set G) : Subgroup G),
          ∀ x, (e x : G) = (x.1 : G) * (x.2 : G)) ∧
        let Y := Subgroup.centralizer (A : Set G)
        let LA := Subgroup.closure (D ∩ (Y : Set G))
        Y < ⊤ ∧ LA < ⊤ ∧ Group.IsPerfect LA ∧ IsUnitaryScalarQuotient q LA ∧
          CFSG.oddCore LA ≤ Subgroup.center LA ∧
          Nat.card (CFSG.oddCore LA) ∣ Nat.gcd 3 (q + 1) ∧
          Nat.card (baseOrbit H LA) = q ^ 3 + 1 ∧
          q ^ 2 + 1 ≤
            Nat.card {ω : rightCosetSpace H | ∀ a ∈ A, rightCosetTranslate H ω a = ω} ∧
          K ≤ LA ∧ D ∩ (Lu : Set G) ∩ (LA : Set G) = D ∩ (K : Set G) ∧
          ¬ LA ≤ Lu ∧ LA ≠ Lu ∧ Lu ⊔ LA = ⊤

end CFSG.ShultStronglyClosedTI.ProperPairModel
