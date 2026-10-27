module

public import CFSG.SignalizerFunctorTheorem.NonLocal.OrthMain
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldBY

public section

open Matrix QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.PartOne
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  (matrixProjectiveConjugationHom_derivedInclusion)

namespace CFSG.SignalizerFunctorTheorem.NonLocal.Orth

variable {K : Type} [Field K] [Finite K] (k : Subfield K) {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)}

theorem orth_centralizer_eq_one (hext : IsExtension k Q₀ Q) (hnd₀ : (polarBilin Q₀).Nondegenerate)
    (hT₀ : ∃ U : Submodule k (Fin d → k), Module.finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0)
    (x : matrixProjectiveDerived Q)
    (hx : ∀ g : matrixDerived Q₀, x * matrixProjectiveProjection Q (inclHom k hext g) =
      matrixProjectiveProjection Q (inclHom k hext g) * x) : x = 1 := by
  obtain ⟨y, rfl⟩ := matrixProjectiveProjection_surjective Q x
  have hκ := matrixProjectiveConjugationHom_derivedInclusion Q y
  have hfix : ∀ j ∈ subfieldDerivedImage k hext,
      matrixProjectiveConjugationHom Q (matrixDerivedInclusion Q y) j = j := by
    intro j hj
    rw [hκ, MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
    obtain ⟨z, rfl⟩ := hj
    obtain ⟨g, rfl⟩ := matrixProjectiveProjection_surjective Q₀ z
    rw [incl_mk]
    exact hx g
  obtain ⟨-, b, hb⟩ :=
    (orthogonal_high_Witt_subfield_pointwise_centralizer K k d Q₀ Q hext hnd₀ hT₀ _).mp hfix
  have hb' : y.val = GeneralLinearGroup.scalar (Fin d) b := by
    rw [matrixDerivedInclusion_val, SemidirectProduct.left_inl] at hb
    exact hb
  rw [matrixProjectiveProjection, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact (mem_matrixDerivedScalars_iff Q y).mpr ⟨b, hb'.symm⟩

theorem nonLocalized_orthogonalSubfield (hext : IsExtension k Q₀ Q)
    (hnd₀ : (polarBilin Q₀).Nondegenerate) (hnd : (polarBilin Q).Nondegenerate)
    (hT₀ : ∃ U : Submodule k (Fin d → k), Module.finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0)
    (hd : 5 ≤ d) (hdq : d ≤ Nat.card k ^ (d - 4)) :
    CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalized (subfieldDerivedImage k hext) :=
  nonLocalized_orthogonalSubfield_of_centralizer k hext hnd₀ hnd hT₀ hd hdq
    (orth_centralizer_eq_one k hext hnd₀ hT₀)

end CFSG.SignalizerFunctorTheorem.NonLocal.Orth
