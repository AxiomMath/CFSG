module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

lemma ggLin_eq_of_pointwise {E : Type*} [Group E] {n : ℕ}
    (ι : Additive E ≃+ (Fin n → ZMod 3)) (e : MulAut E)
    (D : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3))
    (h : ∀ b : E, ι (Additive.ofMul (e b)) = D (ι (Additive.ofMul b))) :
    ggLin (p := 3) ι e = D := by
  refine LinearEquiv.ext fun v => ?_
  rw [ggLin_apply]
  simpa using h (Additive.toMul (ι.symm v))

lemma ggLin_relabel {E : Type*} [Group E] {n : ℕ}
    (ι : Additive E ≃+ (Fin n → ZMod 3))
    (P : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3)) (φ : MulAut E) :
    ggLin (p := 3) (ι.trans P.toAddEquiv) φ = P * ggLin (p := 3) ι φ * P⁻¹ := by
  ext v
  simp only [ggLin_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
    LinearEquiv.coe_toAddEquiv, AddEquiv.trans_apply]
  rfl

lemma ggLin_congr {E : Type*} [Group E] {n : ℕ}
    (ι : Additive E ≃+ (Fin n → ZMod 3)) (e : E ≃* E) (φ : MulAut E) :
    ggLin (p := 3) ι (MulAut.congr e φ) =
      ggLin (p := 3) ι e * ggLin (p := 3) ι φ * (ggLin (p := 3) ι e)⁻¹ := by
  have h : MulAut.congr e φ = e * φ * e⁻¹ := by
    ext x
    simp [MulAut.congr_apply, MulEquiv.trans_apply]
  rw [h, map_mul, map_mul, map_inv]

private lemma toAdditive_trans_self {E E' : Type*} [Group E] [Group E'] {n : ℕ}
    (e : E ≃* E') (ι : Additive E' ≃+ (Fin n → ZMod 3)) :
    (MulEquiv.toAdditive e.symm).trans ((MulEquiv.toAdditive e).trans ι) = ι := by
  ext x
  simp [AddEquiv.trans_apply]

lemma ggLin_trans_congr {E E' : Type} [Group E] [Group E'] {n : ℕ}
    (e : E ≃* E') (ι : Additive E' ≃+ (Fin n → ZMod 3)) (φ : MulAut E) :
    ggLin (p := 3) ((MulEquiv.toAdditive e).trans ι) φ =
      ggLin (p := 3) ι (MulAut.congr e φ) := by
  have h := ggLin_mulEquiv_congr (p := 3) e ((MulEquiv.toAdditive e).trans ι) φ
  rw [toAdditive_trans_self] at h
  exact h.symm

end CFSG.StandardType

end
