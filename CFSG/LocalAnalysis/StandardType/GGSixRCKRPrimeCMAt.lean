module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeDefs

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1
open CFSG.Open (StatedLieTag)

@[expose] def RCKClassicalCompModelAt
    (t : StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L K : Subgroup X) (e : X),
    RCKCompConfig t n f ψ p G₀ A B₁ D J L K e → K ≠ J →
      (∀ a ∈ A, GGPsiInnerDiag (ggU t n f).D ψ a) → RCKClassicalModelID K B₁

@[expose] def RCKRPConfigInnerDiag :
    Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L K : Subgroup X) (e : X),
    RCKCompConfig t n f ψ p G₀ A B₁ D J L K e → ∀ a ∈ A, GGPsiInnerDiag (ggU t n f).D ψ a

theorem rckClassicalCompModel_of_at
    (hID : RCKRPConfigInnerDiag) (h : ∀ t, RCKClassicalTag t → RCKClassicalCompModelAt t) :
    RCKCompModel :=
  fun X _ _ t n f ψ p G₀ A B₁ D J L K e ht hcfg hKJ =>
    h t ht X n f ψ p G₀ A B₁ D J L K e hcfg hKJ (hID X t n f ψ p G₀ A B₁ D J L K e hcfg)

end CFSG.StandardType.RCKRP
