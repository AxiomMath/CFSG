module

public import CFSG.LocalAnalysis.StandardType.GGRootNormInner
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Universal.Spin.Action
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldAction

public section

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal
open Matrix TauCeti
open CFSG.ComponentClassification.CatalogueBHigherLinearField

namespace CFSG.StandardType.LieKnownR2.POmega.Inner

@[expose] def GGSemilinearSimilitude {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (A : GL ι F) (φ : F ≃+* F) (μ : Fˣ) : Prop :=
  ∀ v, Q (A.val *ᵥ (fun i => φ (v i))) = (μ : F) * φ (Q v)

@[expose] def GGMatrixSemilinearAction {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (A : GL ι F) (φ : F ≃+* F) (μ : Fˣ)
    (y : MulAut ↥(spinGroup Q)) : Prop :=
  ∀ x : ↥(spinGroup Q),
    Spin.spinMatrix Q (y x) = A * glFieldEquiv ι φ (Spin.spinMatrix Q x) * A⁻¹

@[expose] def GGTrivialOnNormalizer {K : Type*} [Group K] (R : Subgroup K) (y : MulAut K) :
    Prop :=
  R.map y.toMonoidHom = R ∧
    ∀ n ∈ Subgroup.normalizer (R : Set K),
      y n * n⁻¹ ∈ pCoreOf 2 (Subgroup.normalizer (R : Set K))

end CFSG.StandardType.LieKnownR2.POmega.Inner
