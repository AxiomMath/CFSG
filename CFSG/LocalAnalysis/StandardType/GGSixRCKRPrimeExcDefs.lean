module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeDefs
public import CFSG.LocalAnalysis.StandardType.GGLieCoreBridge
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxToral

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.RCKC1 CFSG.StandardType.GGFinModel CFSG.StandardType.LieCore
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open scoped commutatorElement
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

@[expose] def RCKBridgeFrame
    (t : StatedLieTag) (f p : ℕ) {X : Type} [Group X]
    (G₀ A : Subgroup X) (θ : ↥G₀ →* ModGL (langTag t) GGL)
    (A' : Subgroup (ModGL (langTag t) GGL)) : Prop :=
  θ.ker = Subgroup.center ↥G₀ ∧ θ.range = ⁅ggFixGp t f, ggFixGp t f⁆ ∧
    A' ≤ ggFixGp t f ∧ IsElemAbelian p A' ∧ Nat.card A' = Nat.card A ∧
    (∀ d ∈ A, ∃ a ∈ A', ∀ x : ↥G₀, ∀ h : d * (x : X) * d⁻¹ ∈ G₀, θ ⟨_, h⟩ = a * θ x * a⁻¹) ∧
    (∀ a ∈ A', ∃ d ∈ A, ∀ x : ↥G₀, ∀ h : d * (x : X) * d⁻¹ ∈ G₀, θ ⟨_, h⟩ = a * θ x * a⁻¹)

@[expose] def RCKToralFrame
    (t : StatedLieTag) (f p : ℕ) {X : Type} [Group X]
    (G₀ A : Subgroup X) : Prop :=
  ∃ (θ : ↥G₀ →* ModGL (langTag t) GGL) (A' : Subgroup (ModGL (langTag t) GGL)),
    RCKBridgeFrame t f p G₀ A θ A' ∧ IsToralSubgroup (langTag t) GGL A'

@[expose] def RCKExcToral
    : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L R Rm K : Subgroup X) (e : X), GGExcFive t →
    RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e → K ≠ J → RCKToralFrame t f p G₀ A →
      RCKClassicalModelID K B₁ ∨ GGRootPosNbr K R

@[expose] def RCKExcToralII
    : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L R Rm K : Subgroup X) (e : X), GGExcFive t → GGSixRCKJRow .II J →
    Nat.card R = 2 → RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e → K ≠ J →
      RCKToralFrame t f p G₀ A → RCKClassicalModelID K B₁ ∨ GGRootPosNbr K R

@[expose] def RCKExcCaseVData (t : StatedLieTag) (f p : ℕ) {X : Type} [Group X]
    (G₀ A B₁ : Subgroup X) : Prop :=
  t = .twistedE6 ∧ p = 3 ∧ 3 ∣ 2 ^ f + 1 ∧ ¬ 9 ∣ 2 ^ f + 1 ∧ Nat.card A = 3 ^ 4 ∧ B₁ = A ∧
    A ≤ G₀ ∧ Subgroup.center ↥G₀ = ⊥

@[expose] def RCKExcCaseVReduction
    : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L R Rm K : Subgroup X) (e : X), GGExcFive t →
    RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e → ¬ RCKToralFrame t f p G₀ A →
      RCKExcCaseVData t f p G₀ A B₁

@[expose] def RCKExcCaseVNbr
    : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L R Rm K : Subgroup X) (e : X), GGExcFive t →
    RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e → K ≠ J → RCKExcCaseVData t f p G₀ A B₁ →
      GGRootPosNbr K R

end CFSG.StandardType.RCKRP
