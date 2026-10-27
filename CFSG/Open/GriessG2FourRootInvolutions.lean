module

public import CFSG.Blueprint.Catalog
public import CFSG.Blueprint.ChevalleyPinned

public section

namespace CFSG.Open

open CFSG.Blueprint CFSG.Blueprint.Chevalley Matrix

@[expose] def g2RootNormSq (γ : Fin Tag.G2.rank → ℤ) : ℤ :=
  γ ⬝ᵥ (Tag.G2.symmetrizedCartan *ᵥ γ)

@[expose] def IsG2LongRoot (γ : Fin Tag.G2.rank → ℤ) : Prop :=
  IsRoot .G2 γ ∧ ∀ δ, IsRoot .G2 δ → g2RootNormSq δ ≤ g2RootNormSq γ

@[expose] def IsG2ShortRoot (γ : Fin Tag.G2.rank → ℤ) : Prop :=
  IsRoot .G2 γ ∧ ∀ δ, IsRoot .G2 δ → g2RootNormSq γ ≤ g2RootNormSq δ

@[expose] def IsG2FourLongRootInvolution
    {X : Type} [Group X] (x : X) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
    ∃ (e : X ≃* AdjointQuotient .G2 K) (γ : Fin Tag.G2.rank → ℤ) (s : K)
      (h : pinnedX .G2 K γ s ∈ adjointGroup .G2 K),
      IsG2LongRoot γ ∧ s ≠ 0 ∧
        IsConj (e x) (QuotientGroup.mk (⟨pinnedX .G2 K γ s, h⟩ : adjointGroup .G2 K))

@[expose] def IsG2FourShortRootInvolution
    {X : Type} [Group X] (x : X) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
    ∃ (e : X ≃* AdjointQuotient .G2 K) (γ : Fin Tag.G2.rank → ℤ) (s : K)
      (h : pinnedX .G2 K γ s ∈ adjointGroup .G2 K),
      IsG2ShortRoot γ ∧ s ≠ 0 ∧
        IsConj (e x) (QuotientGroup.mk (⟨pinnedX .G2 K γ s, h⟩ : adjointGroup .G2 K))

end CFSG.Open
