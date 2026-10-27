module

public import CFSG.SignalizerFunctorTheorem.NonLocal.Engine

public noncomputable section

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

variable {K : Type*} [Field K] (F : Type*) [Field F] [Algebra K F] {G : Type*} [Group G]
  {M : Type*} [AddCommMonoid M] [Module K M] {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def matrixRep (b : Module.Basis ι K M) (ρ : G →* Module.End K M) :
    G →* Module.End F (ι → F) :=
  ((NonLocal.extendScalars K F ι).toMonoidHom).comp
    ((LinearMap.toMatrixAlgEquiv b).toAlgHom.toMonoidHom.comp ρ)

theorem matrixRep_injective (b : Module.Basis ι K M) {ρ : G →* Module.End K M}
    (hρ : Function.Injective ρ) : Function.Injective (matrixRep F b ρ) := by
  intro g h hgh
  apply hρ
  have h1 := NonLocal.extendScalars_injective K F ι hgh
  exact (LinearMap.toMatrixAlgEquiv b).injective h1

end CFSG.SignalizerFunctorTheorem.CatalogBridge
