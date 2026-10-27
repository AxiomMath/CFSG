module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwCent
public import CFSG.LieType.Chevalley.LangRootRankOne

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE
  CFSG.LieType.AlgebraicGroups

@[expose] noncomputable def ggKGTwY
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E) :
    twistedE6RootGroup K σ →* ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
  (MulAut.conj F.g0⁻¹).toMonoidHom.comp
    ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (twistedE6RootGroup K σ).subtype)

theorem ggKGTwY_apply
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E)
    (x : twistedE6RootGroup K σ) :
    ggKGTwY F x = F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL TwistTag.E6.tag K) * F.g0 :=
  rfl

@[expose] noncomputable def ggKGTwStep
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ} {E : Subgroup (twistedE6RootGroup K σ)}
    (F : TwE6Frame K σ n p E) :
    ModGL TwistTag.E6.tag (AlgebraicClosure K) →* ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
  (MulAut.conj
    (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) F.v)).toMonoidHom.comp
    (twistHom TwistTag.E6 (AlgebraicClosure K) F.Fr)

@[expose] noncomputable def ggKGTwLhat
    {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} {n p : ℕ} {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E)
    (γ : Fin Tag.E6.rank → ℤ) : Subgroup (ModGL TwistTag.E6.tag (AlgebraicClosure K)) :=
  rootRankOneGroup TwistTag.E6.tag (AlgebraicClosure K) γ ⊓ (ggKGTwStep F).eqLocus (MonoidHom.id _)

@[expose] noncomputable def ggKGTwJ
    {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} {n p : ℕ} {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E)
    (γ : Fin Tag.E6.rank → ℤ) : Subgroup (twistedE6RootGroup K σ) :=
  (ggKGTwLhat F γ).comap (ggKGTwY F)

@[expose] noncomputable def ggKGTwHyp
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)} (F : TwE6Frame K σ n p E)
    (γ : Fin Tag.E6.rank → ℤ) : Subgroup (twistedE6RootGroup K σ) :=
  E ⊓ (Subgroup.centralizer
    ({canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (rootReflection γ)} :
      Set (ModGL TwistTag.E6.tag (AlgebraicClosure K)))).comap (ggKGTwY F)

end CFSG.StandardType
