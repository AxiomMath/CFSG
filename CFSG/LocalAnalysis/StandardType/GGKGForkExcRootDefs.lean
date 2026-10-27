module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcNorm
public import CFSG.LieType.Chevalley.LangRootRankOne

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

@[expose] noncomputable def ggKGExcY
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (F : ExcFrame τ K p E) :
    adjointGroup τ K →* ModGL τ (AlgebraicClosure K) :=
  (MulAut.conj F.D.g0⁻¹).toMonoidHom.comp
    ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup τ K).subtype)

theorem ggKGExcY_apply
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (F : ExcFrame τ K p E) (x : adjointGroup τ K) :
    ggKGExcY F x =
      F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * F.D.g0 :=
  rfl

@[expose] noncomputable def ggKGExcLhat
    (τ : Tag) (K : Type) [Field K]
    (γ : Fin τ.rank → ℤ) : Subgroup (ModGL τ (AlgebraicClosure K)) :=
  (rootRankOneGroup τ K γ).map (baseChangeGL (algebraMap K (AlgebraicClosure K)))

@[expose] noncomputable def ggKGExcJ
    {τ : Tag} {K : Type} [Field K]
    [Finite K] {p : ℕ} {E : Subgroup (adjointGroup τ K)} (F : ExcFrame τ K p E)
    (γ : Fin τ.rank → ℤ) : Subgroup (adjointGroup τ K) :=
  (ggKGExcLhat τ K γ).comap (ggKGExcY F)

@[expose] noncomputable def ggKGExcHyp
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (F : ExcFrame τ K p E) (γ : Fin τ.rank → ℤ) :
    Subgroup (adjointGroup τ K) :=
  E ⊓ (Subgroup.centralizer
    ({canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection γ)} :
      Set (ModGL τ (AlgebraicClosure K)))).comap (ggKGExcY F)

end CFSG.StandardType
