module

public import CFSG.Monster.GMS.S5

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

section Congr

variable {G G' : Type*} [Group G] [Group G'] {a : G} {a' : G'}

@[expose] def gammaAutCongr (φ : twoAGraph a ≃g twoAGraph a') : GammaAut a ≃* GammaAut a' where
  toFun f := φ.symm.trans (f.trans φ)
  invFun f := φ.trans (f.trans φ.symm)
  left_inv f := RelIso.ext fun x => by simp
  right_inv f := RelIso.ext fun x => by simp
  map_mul' f g := RelIso.ext fun x => by simp [RelIso.mul_apply]

@[simp]
theorem gammaAutCongr_apply (φ : twoAGraph a ≃g twoAGraph a') (f : GammaAut a)
    (x : ConjVert a') : gammaAutCongr φ f x = φ (f (φ.symm x)) := rfl

end Congr

end CFSG.Monster.GMS
