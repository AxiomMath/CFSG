module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownOmegaPlusFixed
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaPlus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)

namespace FieldFixOmegaPlus

variable {K : Type} [Field K] [CharP K 2] {m : ℕ}

@[expose] noncomputable def subfieldInj (k : Subfield K) (hm : 1 ≤ m) :
    LargeEvenProj (LargeEvenOmega (LargeEvenQPlus k m)) →*
      LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)) :=
  (RecipeFieldOmega.plusEquiv (K := K) hm).symm.toMonoidHom.comp
    ((inclHom k (coordinateQuadPlus_isExtension k m)).comp
      (RecipeFieldOmega.plusEquiv (K := k) hm).toMonoidHom)

theorem plusEquiv_subfieldInj (k : Subfield K) (hm : 1 ≤ m)
    (y : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus k m))) :
    RecipeFieldOmega.plusEquiv hm (subfieldInj k hm y) =
      inclHom k (coordinateQuadPlus_isExtension k m) (RecipeFieldOmega.plusEquiv hm y) := by
  simp [subfieldInj]

theorem subfieldInj_injective (k : Subfield K) (hm : 1 ≤ m) :
    Function.Injective (subfieldInj k hm) :=
  (RecipeFieldOmega.plusEquiv (K := K) hm).symm.injective.comp
    ((inclHom_injective k (coordinateQuadPlus_isExtension k m)).comp
      (RecipeFieldOmega.plusEquiv (K := k) hm).injective)

theorem mem_range_subfieldInj_iff [Finite K] (k : Subfield K) {σ : K ≃+* K} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hσ : orderOf σ = p) (hσk : ∀ x, x ∈ k ↔ σ x = x)
    (hm : 3 ≤ m)
    {f : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))}
    (hf : MulAut.congr (RecipeFieldOmega.plusEquiv (by omega : 1 ≤ m)) f = AutOm.fieldAutP m σ)
    (r : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) :
    r ∈ (subfieldInj k (by omega : 1 ≤ m)).range ↔ f r = r := by
  have hm1 : 1 ≤ m := by omega
  have hf' : MulAut.congr (RecipeFieldOmega.plusEquiv (K := K) hm1) f =
      AutOm.fieldAutP m σ := hf
  change r ∈ (subfieldInj k hm1).range ↔ f r = r
  let Θ := RecipeFieldOmega.plusEquiv (K := K) hm1
  constructor
  · rintro ⟨y, rfl⟩
    apply Θ.injective
    have h1 : (MulAut.congr Θ f) (Θ (subfieldInj k hm1 y)) =
        Θ (f (subfieldInj k hm1 y)) := by
      rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply]
    rw [← h1, hf', plusEquiv_subfieldInj k hm1 y]
    apply Subtype.ext
    rw [RecipeFieldOmega.fieldAutP_apply_val, inclHom_val]
    exact glFieldAut_glIncl k hσk _
  · intro hr
    have hval : AutOm.fieldAutP m σ (Θ r) = Θ r := by
      have h1 : (MulAut.congr Θ f) (Θ r) = Θ (f r) := by
        rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
          MulEquiv.symm_apply_apply]
      rw [← hf', h1, hr]
    have hfix : glFieldAut (Fin (2 * m)) K σ (Θ r).val = (Θ r).val := by
      have h2 := congrArg (fun X : matrixDerived (coordinateQuadPlus m K) =>
        (X : GL (Fin (2 * m)) K)) hval
      rwa [RecipeFieldOmega.fieldAutP_apply_val] at h2
    obtain ⟨Y, hY⟩ := exists_inclHom_eq_of_fixed k hp hp2 hσ hσk hm hfix
    refine ⟨(RecipeFieldOmega.plusEquiv (K := k) hm1).symm Y, ?_⟩
    apply Θ.injective
    rw [plusEquiv_subfieldInj k hm1, MulEquiv.apply_symm_apply, hY]

end FieldFixOmegaPlus

end CFSG.StandardType

end
