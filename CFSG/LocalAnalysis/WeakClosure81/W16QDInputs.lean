module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveSix
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellThompson
public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs
public import CFSG.LocalAnalysis.WeakClosure81.W16Setup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.QuasithinUnique.Setup.Campbell
open Subgroup

@[expose] def IsU3Shape (X : Type) [Group X] (n : ℕ) : Prop :=
  commutator X = ⊤ ∧ IsPSUGp (X ⧸ Subgroup.center X) 3 n ∧ Nat.card (Subgroup.center X) ∣ 3

@[expose] def W16SixI (G : Type) [Group G] [Finite G] : Prop :=
  Std15 G → ∀ ⦃M V₀ V U S H : Subgroup G⦄, Cex16 M V₀ V U S → IsMinFam16 M U S H →
    ¬ V ≤ pCoreOf 2 H →
      ∃ (X : Type) (_ : Group X) (φ : ↥(conjClosure V H) →* X),
        SevenK.IsBarMap (conjClosure V H) (iSub16 V H) φ ∧
          Shape166 X (SevenK.barSub (conjClosure V H) φ V) (E3.mQuot V (iSub16 V H)) ∧
            ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥

@[expose] def AutRank166Input : Prop :=
  (∀ (X : Type) [Group X] [Finite X] (Y : Subgroup X) (n : ℕ), 1 < n → Nat.card Y = 2 ^ n →
      IsElemAbelian 2 Y → (CFSG.Quasithin.IsPSL 2 2 n X ∨ CFSG.Quasithin.IsSz n X) →
      ∀ E : Subgroup (MulAut X), IsElemAbelian 2 E → (∀ α ∈ E, ∀ y ∈ Y, α y = y) →
        Nat.card E ≤ 2 ^ n) ∧
  (∀ (X : Type) [Group X] [Finite X] (Y : Subgroup X) (n : ℕ), 1 < n → Nat.card Y = 2 ^ n →
      IsElemAbelian 2 Y → IsU3Shape X n →
      ∀ E : Subgroup (MulAut X), IsElemAbelian 2 E → (∀ α ∈ E, ∀ y ∈ Y, α y = y) →
        Nat.card E ≤ 2 ^ (n + 1)) ∧
  (∀ (X : Type) [Group X] [Finite X] (Y : Subgroup X), Nat.card Y = 2 →
      IsElemAbelian 2 Y → Y ⊔ fusionOddCore X = ⊤ →
      (∃ p : ℕ, p.Prime ∧ Nat.card (fusionOddCore X) = p) →
      ∀ E : Subgroup (MulAut X), IsElemAbelian 2 E → (∀ α ∈ E, ∀ y ∈ Y, α y = y) →
        Nat.card E ≤ 2) ∧
  (∀ (X : Type) [Group X] [Finite X] (Y : Subgroup X) (n : ℕ), 1 < n → Nat.card Y = 2 ^ n →
      IsElemAbelian 2 Y →
      (CFSG.Quasithin.IsPSL 2 2 n X ∨ CFSG.Quasithin.IsSz n X ∨ IsU3Shape X n) →
      ∀ α : MulAut X, (∀ y ∈ Y, α y = y) →
        (∀ x : X, (conjSubgroup Y x).map α.toMonoidHom = conjSubgroup Y x) → α = 1)

@[expose] def Borel166Input : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Y P : Subgroup X) (n : ℕ), 1 < n → Nat.card Y = 2 ^ n →
    IsElemAbelian 2 Y → Y ≤ P → IsPGroup 2 P → ¬ 2 ∣ P.index →
    (CFSG.Quasithin.IsSz n X ∨ IsU3Shape X n) →
    ∃ h : X, h ∈ normalizer (Y : Set X) ∧ h ∈ normalizer (P : Set X) ∧ Odd (orderOf h) ∧
      (∀ P₀ : Subgroup X, Y ≤ P₀ → P₀ ≤ P → (∀ x ∈ P₀, h * x * h⁻¹ ∈ P₀) → P₀ = Y ∨ P₀ = P) ∧
      (∀ x ∈ P, h * x * h⁻¹ * x⁻¹ ∈ Y → x ∈ Y)

end CFSG.LocalAnalysis.WeakClosure81

end
