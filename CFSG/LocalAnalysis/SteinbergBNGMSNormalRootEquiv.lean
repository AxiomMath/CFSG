module

public import CFSG.LocalAnalysis.SteinbergBNGMSNormalRootData

public section

namespace CFSG.LocalAnalysis

open Subgroup

variable {D D' : Type*} [Group D] [Group D'] (e : D ≃* D')

theorem map_inf_normalizer_mulEquiv (X U : Subgroup D) :
    (X ⊓ normalizer (U : Set D)).map e.toMonoidHom =
      X.map e.toMonoidHom ⊓ normalizer ((U.map e.toMonoidHom : Subgroup D') : Set D') := by
  rw [Subgroup.map_inf_eq _ _ e.toMonoidHom e.injective, Subgroup.map_equiv_normalizer_eq]

@[expose] def gmsRootEquiv (U : Subgroup D) : U ≃* (U.map e.toMonoidHom : Subgroup D') :=
  e.subgroupMap U

@[simp]
theorem gmsRootEquiv_apply_coe (U : Subgroup D) (u : U) :
    ((gmsRootEquiv e U u : U.map e.toMonoidHom) : D') = e u :=
  MulEquiv.coe_subgroupMap_apply e U u

@[simp]
theorem gmsRootEquiv_symm_apply_coe (U : Subgroup D) (u : U.map e.toMonoidHom) :
    (((gmsRootEquiv e U).symm u : U) : D) = e.symm u :=
  congrArg Subtype.val (MulEquiv.subgroupMap_symm_apply e U u)

def gmsNormalizerEquiv (X U : Subgroup D) :
    (X ⊓ normalizer (U : Set D) : Subgroup D) ≃*
      (X.map e.toMonoidHom ⊓ normalizer ((U.map e.toMonoidHom : Subgroup D') : Set D') :
        Subgroup D') :=
  (gmsRootEquiv e _).trans (MulEquiv.subgroupCongr (map_inf_normalizer_mulEquiv e X U))

@[simp]
theorem gmsNormalizerEquiv_apply_coe (X U : Subgroup D)
    (n : (X ⊓ normalizer (U : Set D) : Subgroup D)) :
    ((gmsNormalizerEquiv e X U n : (X.map e.toMonoidHom ⊓
        normalizer ((U.map e.toMonoidHom : Subgroup D') : Set D') : Subgroup D')) : D') = e n := by
  rw [gmsNormalizerEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    gmsRootEquiv_apply_coe]

end CFSG.LocalAnalysis

end
