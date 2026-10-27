module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRootDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

@[expose] noncomputable def ggRealKGNegLhat
    {τ : Tag} {K : Type} [Field K]
    [Finite K] {p : ℕ} {E : Subgroup (adjointGroup τ K)} (F : ExcFrame τ K p E)
    (γ : Fin τ.rank → ℤ) : Subgroup (ModGL τ (AlgebraicClosure K)) :=
  rootRankOneGroup τ (AlgebraicClosure K) γ ⊓ F.D.step.eqLocus (MonoidHom.id _)

@[expose] noncomputable def ggRealKGNegJ
    {τ : Tag} {K : Type} [Field K]
    [Finite K] {p : ℕ} {E : Subgroup (adjointGroup τ K)} (F : ExcFrame τ K p E)
    (γ : Fin τ.rank → ℤ) : Subgroup (adjointGroup τ K) :=
  (ggRealKGNegLhat F γ).comap (ggKGExcY F)

end CFSG.StandardType
