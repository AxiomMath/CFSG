module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SingerScalar
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairModelAlignment
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthStructure

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FinalChain

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel

variable {G : Type} [Group G]

@[expose] def RootCentralizerTwoCoreConclusion (H : Subgroup G) (z : G)
    (_beta : rightCosetSpace H) (_t : G) : Prop :=
  H ⊓ Subgroup.centralizer (minimalLocalFailurePairActionPointHull H z : Set G) =
    TwoCoreGrowth.pointTwoCoreImage H

@[expose] def RootCentralizerInvolutionsConclusion (H : Subgroup G) (z : G)
    (beta : rightCosetSpace H) (_t : G) : Prop :=
  let B := pairPointStabilizer H beta
  let Q := minimalLocalFailurePairActionPointHull H z
  let C := H ⊓ Subgroup.centralizer (Q : Set G)
  (∀ v ∈ C, v ∉ Q → orderOf v = 2 →
    (∃ ω₁ ω₂ : rightCosetSpace H, ω₁ ≠ ω₂ ∧ rightCosetTranslate H ω₁ v = ω₁ ∧
      rightCosetTranslate H ω₂ v = ω₂) ∧
    ∃ b ∈ B, orderOf b = 2 ∧ ∃ h ∈ H, h⁻¹ * v * h = b) ∧
  ∀ v ∈ TwoCoreGrowth.pointTwoCoreImage H, v ∉ Q → orderOf v = 2 →
    ∃ b ∈ B, orderOf b = 2 ∧ ∃ h ∈ H, h⁻¹ * v * h = b

@[expose] def IsMinimalCentralSection (H Q M A : Subgroup G) : Prop :=
  A ≤ H ∧ (A.subgroupOf H).Normal ∧ Q < A ∧ A ≤ M ∧
    (∀ N : Subgroup G, N ≤ H → (N.subgroupOf H).Normal → Q ≤ N → N ≤ A → N = Q ∨ N = A) ∧
    (∀ a ∈ A, ∀ m ∈ M, a * m * a⁻¹ * m⁻¹ ∈ Q) ∧ ∀ a ∈ A, a ^ 2 ∈ Q

@[expose] def rightOrbit (H A : Subgroup G) (ω : rightCosetSpace H) : Set (rightCosetSpace H) :=
  {ω' | ∃ a ∈ A, rightCosetTranslate H ω a = ω'}

@[expose] def setTranslate (H : Subgroup G) (O : Set (rightCosetSpace H)) (g : G) :
    Set (rightCosetSpace H) :=
  (fun ω => rightCosetTranslate H ω g) '' O

@[expose] def orbitsOffBase (H A : Subgroup G) : Set (Set (rightCosetSpace H)) :=
  {O | ∃ ω, ω ≠ rightCosetMk H 1 ∧ O = rightOrbit H A ω}

@[expose] def conjSet (S : Set G) (h : G) : Set G :=
  (fun g => h⁻¹ * g * h) '' S

@[expose] def involutionCoset (Q : Subgroup G) (u : G) : Set G :=
  (fun y => u * y) '' (Q : Set G)

@[expose] def cosetConjugates (H Q : Subgroup G) (u : G) : Set (Set G) :=
  {D | ∃ h ∈ H, D = conjSet (involutionCoset Q u) h}

@[expose] def InvolutionCountConclusion (H : Subgroup G) (z : G) (beta : rightCosetSpace H)
    (t : G) : Prop :=
  let B := pairPointStabilizer H beta
  let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
  let K := minimalLocalFailureProperPairHull H z beta t
  let Q := minimalLocalFailurePairActionPointHull H z
  let q := Nat.card Q
  let M := TwoCoreGrowth.pointTwoCoreImage H
  let J := Subgroup.centralizer (K : Set G)
  M = H ⊓ Subgroup.centralizer (Q : Set G) ∧
    J ≠ ⊥ ∧ IsElemAbelian 2 J ∧ M ⊓ B = J ∧
    Q ⊓ J = ⊥ ∧ J ≤ Subgroup.centralizer (Q : Set G) ∧
    (∀ j ∈ J, j ≠ 1 → M ⊓ Subgroup.centralizer ({j} : Set G) = Q ⊔ J) ∧
    (∀ x ∈ X, x ≠ 1 → M ⊓ Subgroup.centralizer ({x} : Set G) = J) ∧
    (∀ j ∈ J, j ≠ 1 → ∀ k ∈ J, k ≠ 1 →
      (k ∈ conjugacyWithin H j ↔ k ∈ conjugacyWithin B j)) ∧
    (∀ j ∈ J, j ≠ 1 →
      Nat.card (conjugacyWithin H j) = q ^ 2 * Nat.card (conjugacyWithin B j)) ∧
    ∀ U : Subgroup G, U ≤ H → (U.subgroupOf H).Normal → Q ≤ U → U ≤ M →
      Nat.card {u : U // orderOf u = 2} = q - 1 + q ^ 2 * (Nat.card (U ⊓ J : Subgroup G) - 1) ∧
      (U ⊓ J = ⊥ → {u : G | u ∈ U ∧ orderOf u = 2} = (Q : Set G) \ {1})

@[expose] def CentralSectionConclusion (H : Subgroup G) (z : G) (beta : rightCosetSpace H)
    (t : G) : Prop :=
  let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
  let K := minimalLocalFailureProperPairHull H z beta t
  let Q := minimalLocalFailurePairActionPointHull H z
  let q := Nat.card Q
  let M := TwoCoreGrowth.pointTwoCoreImage H
  let J := Subgroup.centralizer (K : Set G)
  (∃ A : Subgroup G, IsMinimalCentralSection H Q M A) ∧
    ∀ A : Subgroup G, IsMinimalCentralSection H Q M A →
      A ⊓ J = ⊥ ∧ Nat.card A = q ^ 2 ∧
      (∀ e : ℕ, q = 2 ^ e → Nonempty (A ≃* Multiplicative (Fin e → ZMod 4))) ∧
      {a : G | a ∈ A ∧ orderOf a = 2} = (Q : Set G) \ {1} ∧
      (∀ x ∈ X, x ≠ 1 → A ⊓ Subgroup.centralizer ({x} : Set G) = ⊥ ∧
        ∀ a ∈ A, a⁻¹ * (x * a * x⁻¹) ∈ Q → a ∈ Q) ∧
      (∀ j ∈ J, j ≠ 1 → A ⊓ Subgroup.centralizer ({j} : Set G) = Q ∧
        ∃ φ : A →* Q, (∀ a : A, (φ a : G) = (a : G) * j * (a : G)⁻¹ * j⁻¹) ∧
          φ.ker = Q.subgroupOf A ∧ Function.Surjective φ ∧
          ∀ x ∈ X, ∀ a a' : A, (a' : G) = x * a * x⁻¹ → (φ a' : G) = x * φ a * x⁻¹) ∧
      ∃ ψ : A →* Q, (∀ a : A, (ψ a : G) = (a : G) ^ 2) ∧
        ψ.ker = Q.subgroupOf A ∧ Function.Surjective ψ ∧
        ∀ x ∈ X, ∀ a a' : A, (a' : G) = x * a * x⁻¹ → (ψ a' : G) = x * ψ a * x⁻¹

@[expose] def FourSectionConclusion (H : Subgroup G) (z : G) (beta : rightCosetSpace H) (t : G)
    (A : Subgroup G) : Prop :=
  let B := pairPointStabilizer H beta
  let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
  let K := minimalLocalFailureProperPairHull H z beta t
  let Q := minimalLocalFailurePairActionPointHull H z
  let J := Subgroup.centralizer (K : Set G)
  let Λ := orbitsOffBase H A
  ∃ u : G, orderOf u = 2 ∧ (J : Set G) = {1, u} ∧ (∀ a ∈ A, u * a * u⁻¹ = a⁻¹) ∧
    Nat.card Λ = Nat.card Q ∧
    (∀ h ∈ H, ∀ O ∈ Λ, setTranslate H O h ∈ Λ) ∧
    (∀ O₁ ∈ Λ, ∀ O₂ ∈ Λ, ∀ O₃ ∈ Λ, ∀ O₄ ∈ Λ, O₁ ≠ O₂ → O₃ ≠ O₄ →
      ∃ h ∈ H, setTranslate H O₁ h = O₃ ∧ setTranslate H O₂ h = O₄) ∧
    (∀ j ∈ J, ∀ O ∈ Λ, setTranslate H O j = O) ∧
    (∀ x ∈ X, setTranslate H (rightOrbit H A beta) x = rightOrbit H A beta) ∧
    (∀ O ∈ Λ, ∀ O' ∈ Λ, O ≠ rightOrbit H A beta → O' ≠ rightOrbit H A beta →
      ∃! x : X, setTranslate H O x = O') ∧
    {h : G | h ∈ H ∧ conjSet (involutionCoset Q u) h = involutionCoset Q u} =
      ((A ⊔ B : Subgroup G) : Set G) ∧
    Nat.card (cosetConjugates H Q u) = Nat.card Q ∧
    (∃ f : Set G → Set (rightCosetSpace H), Set.BijOn f (cosetConjugates H Q u) Λ ∧
      f (involutionCoset Q u) = rightOrbit H A beta ∧
      ∀ h ∈ H, ∀ D ∈ cosetConjugates H Q u, f (conjSet D h) = setTranslate H (f D) h) ∧
    (∀ D ∈ cosetConjugates H Q u, ∀ D' ∈ cosetConjugates H Q u,
      D ≠ involutionCoset Q u → D' ≠ involutionCoset Q u → ∃! x : X, conjSet D x = D') ∧
    ∀ g ∈ A ⊔ J, ∀ D ∈ cosetConjugates H Q u, conjSet D g = D

@[expose] def IndexDichotomyConclusion (H : Subgroup G) (z : G) (beta : rightCosetSpace H)
    (t : G) (A : Subgroup G) : Prop :=
  let B := pairPointStabilizer H beta
  let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
  let K := minimalLocalFailureProperPairHull H z beta t
  let Q := minimalLocalFailurePairActionPointHull H z
  let q := Nat.card Q
  let M := TwoCoreGrowth.pointTwoCoreImage H
  let J := Subgroup.centralizer (K : Set G)
  ((A ⊔ J).relIndex M = 1 ∨ (A ⊔ J).relIndex M = q) ∧
    ((A ⊔ J).relIndex M = q →
      Nat.card M = 2 * q ^ 3 ∧ H = M ⊔ B ∧
      (∀ u ∈ J, u ≠ 1 → ∀ D ∈ cosetConjugates H Q u, ∀ D' ∈ cosetConjugates H Q u,
        ∃ m ∈ M, conjSet D m = D') ∧
      ((A ⊔ J).subgroupOf H).Normal ∧
      (∀ m ∈ M, m ^ 2 ∈ A ⊔ J) ∧ (∀ m ∈ M, ∀ m' ∈ M, m * m' * m⁻¹ * m'⁻¹ ∈ A ⊔ J) ∧
      ∀ m ∈ M, m ∉ A ⊔ J → ∀ m' ∈ M, m' ∉ A ⊔ J →
        ∃! x : X, m'⁻¹ * ((x : G) * m * (x : G)⁻¹) ∈ A ⊔ J)

@[expose] def LargeBranchExcludedConclusion (H : Subgroup G) (z : G) (beta : rightCosetSpace H)
    (t : G) (A : Subgroup G) : Prop :=
  (A ⊔ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G)).relIndex
      (TwoCoreGrowth.pointTwoCoreImage H) ≠
    Nat.card (minimalLocalFailurePairActionPointHull H z)

@[expose] def SingerQuotientConclusion (H : Subgroup G) (z : G) (beta : rightCosetSpace H)
    (t : G) (A : Subgroup G) : Prop :=
  let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
  let K := minimalLocalFailureProperPairHull H z beta t
  let Q := minimalLocalFailurePairActionPointHull H z
  let q := Nat.card Q
  let M := TwoCoreGrowth.pointTwoCoreImage H
  let J := Subgroup.centralizer (K : Set G)
  ∃ u : G, orderOf u = 2 ∧ (J : Set G) = {1, u} ∧
    M = A ⊔ Subgroup.zpowers u ∧ A ⊓ Subgroup.zpowers u = ⊥ ∧ (∀ a ∈ A, u * a * u⁻¹ = a⁻¹) ∧
    ∀ e : ℕ, q = 2 ^ e →
      Nonempty (A ≃* Multiplicative (Fin e → ZMod 4)) ∧ Even e ∧ 4 ≤ e ∧
      ∃ d : ℕ, d ∣ e ∧
        ∃ (F : Type) (_ : Field F) (_ : Algebra (ZMod 2) F), Nat.card F = q ∧
          ∃ (φ : Q ≃* Multiplicative F) (ρ : H →* (F ≃ₗ[ZMod 2] F)),
            ρ.ker = M.subgroupOf H ∧
            (∀ (h : H) (x y : Q), (y : G) = h * x * (h : G)⁻¹ →
              (φ y).toAdd = ρ h (φ x).toAdd) ∧
            (X.subgroupOf H).map ρ = Singer.scalars (ZMod 2) F ∧
            Singer.scalars (ZMod 2) F ≤ ρ.range ∧
            Nat.card ρ.range = q * (q - 1) * d ∧
            CFSG.pCore 2 ρ.range = ⊥

end CFSG.ShultStronglyClosedTI.FinalChain
