module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldReeG2
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeOuter

public section

open CFSG.LieType.Ree (ReeTag)
open CFSG.ComponentClassification.LiteratureLocal.SmallRee (frobeniusΓ frobRing
  exists_eq_conj_mul_frobeniusΓ_pow)

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem frobeniusΓ_eq_reeGammaFieldAut
    {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] :
    (frobeniusΓ : MulAut (ReeTag.G2.reeGamma K a)) =
      ReeTag.G2.reeGammaFieldAut K a (frobRing : K ≃+* K) :=
  MulEquiv.ext fun _ => Subtype.ext rfl

theorem smallReeOuterIsField :
    SmallReeOuterIsField := by
  intro a ha K _ _ _ hK α
  obtain ⟨g, k, hα⟩ := exists_eq_conj_mul_frobeniusΓ_pow ha hK α
  refine ⟨g, (frobRing : K ≃+* K) ^ k, ?_⟩
  rw [hα, frobeniusΓ_eq_reeGammaFieldAut, ← ReeTag.reeGammaFieldAutHom_apply, ← map_pow,
    ReeTag.reeGammaFieldAutHom_apply]

end CFSG.SignalizerFunctorTheorem.CatalogBridge
