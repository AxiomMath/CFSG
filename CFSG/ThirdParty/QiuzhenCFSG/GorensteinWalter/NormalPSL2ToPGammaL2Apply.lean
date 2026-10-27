module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2NormalExtension

namespace CFSG
end CFSG
open CFSG

/-!
# The normal-extension embedding on its `PSL₂` core
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix

universe u

/-- On the distinguished normal subgroup, the semilinear normal-extension
embedding is the canonical inner `PSL₂ → PGL₂ → PΓL₂` map. -/
public theorem normalPSL2ToPGammaL2_apply_subtype
    {R : Type u} [Group R]
    (N : Subgroup R) [N.Normal]
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (e : N ≃* PSL2 K)
    (hsurj : Function.Surjective (pGammaL2ToMulAutPSL2 K hK hcard))
    (n : N) :
    normalPSL2ToPGammaL2 N K hK hcard e hsurj (n : R) =
      SemidirectProduct.inl
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (e n)) := by
  apply (pGammaL2EquivMulAutPSL2 K hK hcard hsurj).injective
  simp only [normalPSL2ToPGammaL2, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  simp only [pGammaL2EquivMulAutPSL2, MulEquiv.ofBijective_apply,
    normalPSL2ConjAction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  change MulAut.congr e (MulAut.conjNormal (n : R)) =
    pGammaL2ToMulAutPSL2 K hK hcard
      (SemidirectProduct.inl
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (e n)))
  rw [pGammaL2ToMulAutPSL2_inl]
  rw [pgl2InnerAutPSL2_toPGL]
  rw [MulAut.conjNormal_val]
  ext x
  simp [MulAut.congr, MulAut.conj_apply]

end CFSG.GorensteinWalter
