module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.RankThree.OddKernel.InvolutionDims

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.OddKernel

open Module CFSG.SectionRank.Ccomm

variable {p : ℕ} [hp : Fact p.Prime] {W : Type*} [Group W] {n : ℕ}

@[expose] noncomputable def coordLin (e : W ≃* Multiplicative (Fin n → ZMod p)) (σ : MulAut W) :
    (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p) :=
  Matrix.toLin' (elemAutEquivGL e σ : Matrix (Fin n) (Fin n) (ZMod p))

theorem coordLin_apply (e : W ≃* Multiplicative (Fin n → ZMod p)) (σ : MulAut W) (w : W) :
    coordLin e σ (Multiplicative.toAdd (e w)) = Multiplicative.toAdd (e (σ w)) := by
  rw [coordLin, Matrix.toLin'_apply, elemAutEquivGL_mulVec]

theorem coordLin_apply' (e : W ≃* Multiplicative (Fin n → ZMod p)) (σ : MulAut W)
    (v : Fin n → ZMod p) :
    coordLin e σ v = Multiplicative.toAdd (e (σ (e.symm (Multiplicative.ofAdd v)))) := by
  rw [← coordLin_apply, MulEquiv.apply_symm_apply, toAdd_ofAdd]

theorem coordLin_mul (e : W ≃* Multiplicative (Fin n → ZMod p)) (σ τ : MulAut W) :
    coordLin e (σ * τ) = coordLin e σ ∘ₗ coordLin e τ := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, coordLin_apply', coordLin_apply', coordLin_apply', ofAdd_toAdd,
    MulEquiv.symm_apply_apply, MulAut.mul_apply]

theorem coordLin_one (e : W ≃* Multiplicative (Fin n → ZMod p)) :
    coordLin e 1 = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  rw [coordLin_apply', MulAut.one_apply, MulEquiv.apply_symm_apply, toAdd_ofAdd,
    LinearMap.id_apply]

theorem coordLin_injective (e : W ≃* Multiplicative (Fin n → ZMod p)) :
    Function.Injective (coordLin e) := by
  intro σ τ h
  ext w
  have := congrArg (fun L => L (Multiplicative.toAdd (e w))) h
  simp only [coordLin_apply] at this
  exact e.injective (Multiplicative.toAdd.injective this)

theorem coordLin_involution (e : W ≃* Multiplicative (Fin n → ZMod p)) {σ : MulAut W}
    (hσ : σ * σ = 1) (v : Fin n → ZMod p) : coordLin e σ (coordLin e σ v) = v := by
  rw [← LinearMap.comp_apply, ← coordLin_mul, hσ, coordLin_one, LinearMap.id_apply]

theorem coordLin_comm (e : W ≃* Multiplicative (Fin n → ZMod p)) {σ τ : MulAut W}
    (h : σ * τ = τ * σ) (v : Fin n → ZMod p) :
    coordLin e σ (coordLin e τ v) = coordLin e τ (coordLin e σ v) := by
  rw [← LinearMap.comp_apply, ← coordLin_mul, h, coordLin_mul, LinearMap.comp_apply]

theorem det_coordLin (e : W ≃* Multiplicative (Fin n → ZMod p)) (σ : MulAut W) :
    LinearMap.det (coordLin e σ) =
      ((Matrix.GeneralLinearGroup.det (elemAutEquivGL e σ) : (ZMod p)ˣ) : ZMod p) := by
  rw [coordLin, LinearMap.det_toLin', Matrix.GeneralLinearGroup.val_det_apply]

theorem coordLin_eq_neg_iff (e : W ≃* Multiplicative (Fin n → ZMod p)) (σ : MulAut W) :
    (∀ v, coordLin e σ v = -v) ↔ ∀ w : W, σ w = w⁻¹ := by
  rw [← elemAutEquivGL_eq_neg_one_iff e σ]
  constructor
  · intro h
    apply Units.ext
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Units.val_neg, Units.val_one, map_neg, Matrix.toLin'_one, LinearMap.neg_apply,
      LinearMap.id_apply, ← h v]
    rfl
  · intro h v
    rw [coordLin, h, Units.val_neg, Units.val_one, map_neg, Matrix.toLin'_one,
      LinearMap.neg_apply, LinearMap.id_apply]

theorem card_fixed_eq_pow [Finite W] (e : W ≃* Multiplicative (Fin n → ZMod p))
    (σ : MulAut W) :
    Nat.card {w : W // σ w = w} = p ^ finrank (ZMod p) (fixSpace (coordLin e σ)) := by
  have eqv : {w : W // σ w = w} ≃ fixSpace (coordLin e σ) :=
    { toFun := fun w => ⟨Multiplicative.toAdd (e w), by
        rw [mem_fixSpace, coordLin_apply, w.2]⟩
      invFun := fun v => ⟨e.symm (Multiplicative.ofAdd v), by
        have hv := mem_fixSpace.1 v.2
        rw [coordLin_apply'] at hv
        apply e.injective
        apply Multiplicative.toAdd.injective
        rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
        exact hv⟩
      left_inv := fun w => Subtype.ext (by simp)
      right_inv := fun v => Subtype.ext (by simp) }
  rw [Nat.card_congr eqv, Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]

end CFSG.RankThree.OddKernel
