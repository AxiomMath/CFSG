module

public import CFSG.LocalAnalysis.StandardType.GGE6DepModelDefs

public section

namespace CFSG.StandardType

namespace E6Dep

variable {G : Type} [Group G] {Bs : Subgroup G}

@[expose] def ActsAs (ι : Additive ↥Bs ≃+ Vec6) (φ : MulAut ↥Bs) (g : Mat6) : Prop :=
  ∀ b : ↥Bs, ι (Additive.ofMul (φ b)) = g.mulVec (ι (Additive.ofMul b))

theorem ActsAs.mul {ι : Additive ↥Bs ≃+ Vec6} {φ ψ : MulAut ↥Bs} {g h : Mat6}
    (hφ : ActsAs ι φ g) (hψ : ActsAs ι ψ h) : ActsAs ι (φ * ψ) (g * h) := by
  intro b
  rw [MulAut.mul_apply, hφ (ψ b), hψ b, Matrix.mulVec_mulVec]

theorem ActsAs.one (ι : Additive ↥Bs ≃+ Vec6) : ActsAs ι (1 : MulAut ↥Bs) 1 := by
  intro b
  rw [MulAut.one_apply, Matrix.one_mulVec]

end E6Dep

end CFSG.StandardType

end
