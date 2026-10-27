module

public import CFSG.LocalAnalysis.StandardType.GGLangRatLift

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
open scoped TensorProduct

@[expose] def LangRatRootFactor {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ))
    (h : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) : Prop :=
  ∃ l : List ((Fin τ.rank → ℤ) × (Fin τ.rank → ℤ)),
    (∀ p ∈ l, p.1 ∈ Ψ ∧ p.2 ∈ Submodule.span ℤ Ψ) ∧
      ∀ x ∈ Submodule.span ℤ Ψ, h x = (l.map fun p => iform x p.1 • p.2).sum

@[expose] def LangRatSqInnerOrDet : Prop :=
  ∀ (τ : Tag), (τ = .E7 ∨ τ = .E8) → ∀ (Ψ : Set (Fin τ.rank → ℤ)), IsRootComponent Ψ →
    ∀ σ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ), Set.BijOn σ Ψ Ψ →
      (∀ γ ∈ Ψ, ∀ δ ∈ Ψ, iform (σ γ) (σ δ) = iform γ δ) → (∀ γ ∈ Ψ, σ (-γ) = -σ γ) →
      twistInner Ψ (σ^[2]) ∨
        (Matrix.of fun α β : ↥(simpleRoots Ψ) => iform (α : Fin τ.rank → ℤ) β).det ∣ 4

end CFSG.StandardType.LangRat
