module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldGlue
public import CFSG.LieType.Chevalley.EvenTrialityCanonicalFieldCentralizer
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6OddField
public import CFSG.LieType.Ree.SmallReeOuterThreeKernel
public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.FieldAut
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms

public section

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint.Chevalley CFSG.Blueprint CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (subfieldDerivedImage coordinateQuadOdd_isExtension
  coordinateQuadPlus_isExtension coordinateQuadMinus_isExtension)
open CFSG.Blueprint (suzukiGroup)
open CFSG.LieType.Ree (ReeTag)
open CFSG.RankThree.Chevalley (subfieldRootGroupImage)
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

@[expose] def SubfieldNonLocalizedPSL : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 3 ≤ n → ∀ p : ℕ, p.Prime → Odd p →
    ¬ p ∣ Nat.card (LinearFlag.projectiveSL n K) → ∀ σ : K ≃+* K, orderOf σ = p →
      FStarSimple (signalizerFixedSubgroup (LinearFlag.fieldAut n K σ)) →
      NonLocalized (signalizerFixedSubgroup (LinearFlag.fieldAut n K σ))

@[expose] def SubfieldNonLocalizedPSp : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (r : ℕ), 2 ≤ r → ∀ p : ℕ, p.Prime → Odd p →
    ¬ p ∣ Nat.card (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp r K)) →
    ∀ σ : K ≃+* K, orderOf σ = p →
      FStarSimple (signalizerFixedSubgroup (SymplecticHigher.fieldAut r K σ)) →
      NonLocalized (signalizerFixedSubgroup (SymplecticHigher.fieldAut r K σ))

@[expose] def SubfieldNonLocalizedPSU : Prop :=
  ∀ {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) (n : ℕ), 3 ≤ n → ∀ p : ℕ,
    p.Prime → Odd p → ¬ (n = 3 ∧ ℓ = 2 ∧ f = p) →
    ¬ p ∣ Nat.card (UnitaryHigher.primeFormP h ((1 : Matrix.GeneralLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) →
    ∀ σ : K ≃+* K, orderOf σ = p →
      FStarSimple (signalizerFixedSubgroup
        (UnitaryHigher.primeFormFieldHom h (UnitaryHigher.isPrimeFormGram_one (n := n)) σ)) →
      NonLocalized (signalizerFixedSubgroup
        (UnitaryHigher.primeFormFieldHom h (UnitaryHigher.isPrimeFormGram_one (n := n)) σ))

@[expose] def SubfieldNonLocalizedOrthogonal : Prop :=
  (∀ n ℓ e p : ℕ, StatedLieAdmissible .POmegaOdd n ℓ e → p.Prime → 3 < p → p ≠ ℓ →
    ∀ (K : Type) [Field K] [Finite K] (k : Subfield K), Nat.card k = ℓ ^ e →
      Nat.card K = ℓ ^ (e * p) → ∀ σ : K ≃+* K, orderOf σ = p → (∀ x, x ∈ k ↔ σ x = x) →
        NonLocalized (subfieldDerivedImage k (coordinateQuadOdd_isExtension k n))) ∧
  (∀ n ℓ e p : ℕ, StatedLieAdmissible .POmegaPlus n ℓ e → p.Prime → 3 < p → p ≠ ℓ →
    ∀ (K : Type) [Field K] [Finite K] (k : Subfield K), Nat.card k = ℓ ^ e →
      Nat.card K = ℓ ^ (e * p) → ∀ σ : K ≃+* K, orderOf σ = p → (∀ x, x ∈ k ↔ σ x = x) →
        NonLocalized (subfieldDerivedImage k (coordinateQuadPlus_isExtension k n))) ∧
  (∀ n ℓ e p : ℕ, StatedLieAdmissible .POmegaMinus n ℓ e → p.Prime → 3 < p → p ≠ ℓ →
    ∀ (hn : 1 ≤ n) (K : Type) [Field K] [Finite K] (k : Subfield K), Nat.card k = ℓ ^ e →
      Nat.card K = ℓ ^ (e * p) → ∀ σ : K ≃+* K, orderOf σ = p → (∀ x, x ∈ k ↔ σ x = x) →
        ∀ b c' : k, (∀ s : k, s ^ 2 + b * s + c' ≠ 0) →
          NonLocalized (subfieldDerivedImage k (coordinateQuadMinus_isExtension k n hn b c')))

@[expose] def SubfieldNonLocalizedChevalley
    : Prop :=
  ∀ (τ : Tag), (τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
    ∀ (K : Type) [Field K] [Finite K], IsSimpleGroup (adjointGroup τ K) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card (adjointGroup τ K) →
        ∀ σ : K ≃+* K, orderOf σ = p →
          NonLocalized ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K))

@[expose] def SubfieldNonLocalizedSuzuki : Prop :=
  ∀ (a : ℕ), 1 ≤ a → ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ (2 * a + 1) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 2 * a + 1 → ∀ σ : K ≃+* K, orderOf σ = p →
      NonLocalized (signalizerFixedSubgroup (szFieldAut a K σ))

@[expose] def SubfieldNonLocalizedTriality
    : Prop :=
  ∀ (ℓ d p : ℕ), ℓ.Prime → 1 ≤ d → p.Prime → 3 < p →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ (3 * d * p) →
      ∀ σ δ : K ≃+* K, (∀ c, σ c = c ^ ℓ ^ (d * p)) → (∀ c, δ c = c ^ ℓ ^ (3 * d)) →
        NonLocalized ((trialityFieldImage σ δ).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))

@[expose] def SubfieldNonLocalizedTrialityTwo
    : Prop :=
  ∀ (p : ℕ), p.Prime → 3 < p → ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ (3 * p) →
    ∀ σ δ : K ≃+* K, (∀ c, σ c = c ^ 2 ^ p) → (∀ c, δ c = c ^ 2 ^ 3) →
      NonLocalized ((trialityFieldImage σ δ).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))

@[expose] def SubfieldNonLocalizedTwistedE6
    : Prop :=
  ∀ (ℓ d p : ℕ), ℓ.Prime → 1 ≤ d → p.Prime → 3 < p →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ (2 * d * p) →
      ∀ (κ σ : K ≃+* K) (σ₀ : fixSubfield κ ≃+* fixSubfield κ), (∀ c, κ c = c ^ ℓ ^ (2 * d)) →
        (∀ c, σ c = c ^ ℓ ^ (d * p)) → (∀ c, (σ₀ c : K) = (c : K) ^ ℓ ^ d) →
          NonLocalized ((subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀).subgroupOf
            (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))

@[expose] def SubfieldNonLocalizedTwistedE6Small
    : Prop :=
  ∀ (ℓ d p : ℕ), ℓ.Prime → 1 ≤ d → p.Prime → 3 < p → (ℓ = 2 ∨ ℓ = 3) → d = 1 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ (2 * d * p) →
      ∀ (κ σ : K ≃+* K) (σ₀ : fixSubfield κ ≃+* fixSubfield κ), (∀ c, κ c = c ^ ℓ ^ (2 * d)) →
        (∀ c, σ c = c ^ ℓ ^ (d * p)) → (∀ c, (σ₀ c : K) = (c : K) ^ ℓ ^ d) →
          NonLocalized ((subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀).subgroupOf
            (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))

@[expose] def SubfieldNonLocalizedSmallRee
    : Prop :=
  ∀ (a : ℕ), 1 ≤ a → ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.G2.prime],
    Nat.card K = 3 ^ (2 * a + 1) → ∀ p : ℕ, p.Prime → 3 < p → ∀ σ : K ≃+* K, orderOf σ = p →
      NonLocalized (signalizerFixedSubgroup (ReeTag.G2.reeGammaFieldAut K a σ))

@[expose] def SubfieldNonLocalizedLargeRee
    : Prop :=
  ∀ (a : ℕ), 1 ≤ a → ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime],
    Nat.card K = 2 ^ (2 * a + 1) → ∀ p : ℕ, p.Prime → 3 < p → ∀ σ : K ≃+* K, orderOf σ = p →
      NonLocalized (signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ))

@[expose] def SubfieldNonLocalizedSmallReeBZero
    : Prop :=
  ∀ (a : ℕ), 1 ≤ a → ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.G2.prime],
    Nat.card K = 3 ^ (2 * a + 1) → ∀ p : ℕ, p.Prime → 3 < p → p = 2 * a + 1 →
      ∀ σ : K ≃+* K, orderOf σ = p →
        NonLocalized (signalizerFixedSubgroup (ReeTag.G2.reeGammaFieldAut K a σ))

@[expose] def SubfieldNonLocalizedLargeReeBZero
    : Prop :=
  ∀ (a : ℕ), 1 ≤ a → ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime],
    Nat.card K = 2 ^ (2 * a + 1) → ∀ p : ℕ, p.Prime → 3 < p → p = 2 * a + 1 →
      ∀ σ : K ≃+* K, orderOf σ = p →
        NonLocalized (signalizerFixedSubgroup (ReeTag.F4.reeGammaFieldAut K a σ))

end CFSG.SignalizerFunctorTheorem.CatalogBridge
