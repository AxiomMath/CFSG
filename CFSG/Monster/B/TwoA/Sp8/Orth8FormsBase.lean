
module

public import CFSG.Monster.B.TwoA.Sp8.GenActionHomBase
public import CFSG.Monster.B.TwoA.Sp8.QuadCosetBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA

@[expose] def qv (v : V8) : QuadraticForm (ZMod 2) V8 :=
  qForm + QuadraticMap.linMulLin (b0 v) (b0 v)

theorem qv_apply (v w : V8) : qv v w = qPoly w + b0 v w := by
  change qForm w + QuadraticMap.linMulLin (b0 v) (b0 v) w = _
  rw [QuadraticMap.linMulLin_apply, qForm_apply, zmod2_mul_self]

theorem b0_comm (v w : V8) : b0 v w = b0 w v := by
  rw [← polarBilin_qForm, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]

theorem qv_apply' (v w : V8) : qv v w = qPoly (w + v) + qPoly v := by
  rw [qv_apply, b0_comm, b0_eq_qPoly]
  ring_nf
  simp only [sub_eq_add_neg, ZModModule.neg_eq_self]

theorem polarBilin_qv (v : V8) : QuadraticMap.polarBilin (qv v) = b0 := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, qv_apply, qv_apply, qv_apply,
    map_add, b0_eq_qPoly x y]
  ring

theorem qv_zero : qv 0 = qForm := by
  ext w
  rw [qv_apply, map_zero, LinearMap.zero_apply, add_zero, qForm_apply]

theorem qv_injective : Function.Injective qv := by
  intro v w h
  have h1 : ∀ u, b0 v u = b0 w u := fun u => by
    have := congrArg (fun Q : QuadraticForm (ZMod 2) V8 => Q u) h
    simp only [qv_apply] at this
    exact add_left_cancel this
  have h2 : ∀ u, b0 (v - w) u = 0 := fun u => by rw [map_sub, LinearMap.sub_apply, h1, sub_self]
  exact sub_eq_zero.1 (nondegenerate_b0.1 _ h2)

theorem exists_qv_eq (Q : QuadraticForm (ZMod 2) V8) (hQ : QuadraticMap.polarBilin Q = b0) :
    ∃ v, qv v = Q := by
  have hadd : ∀ x y, Q (x + y) - qForm (x + y) = (Q x - qForm x) + (Q y - qForm y) := by
    intro x y
    have h1 := congrArg (fun B : LinearMap.BilinForm (ZMod 2) V8 => B x y)
      (hQ.trans polarBilin_qForm.symm)
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar] at h1
    linear_combination h1
  let ℓ : V8 →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun w => Q w - qForm w
      map_add' := hadd
      map_smul' := fun c w => by
        rcases zmod2_cases c with rfl | rfl
        · simp
        · simp }
  obtain ⟨v, hv⟩ : ∃ v, b0.toDual nondegenerate_b0 v = ℓ :=
    ⟨(b0.toDual nondegenerate_b0).symm ℓ, LinearEquiv.apply_symm_apply _ _⟩
  refine ⟨v, ?_⟩
  ext w
  have hw : b0 v w = Q w - qForm w := by
    rw [← LinearMap.BilinForm.toDual_def nondegenerate_b0, hv]
    rfl
  rw [qv_apply, hw, qForm_apply]
  ring

@[expose] def minusForms : Set (QuadraticForm (ZMod 2) V8) :=
  {Q | QuadraticMap.polarBilin Q = b0 ∧
    QuadraticMap.Equivalent Q (CFSG.LieType.Universal.Spin.quadMinus 4 (ZMod 2) 1 1)}

theorem card_zeros_of_equivalent {Q Q' : QuadraticForm (ZMod 2) V8}
    (e : QuadraticMap.IsometryEquiv Q Q') :
    (Finset.univ.filter fun w => Q w = 0).card = (Finset.univ.filter fun w => Q' w = 0).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (e.toLinearEquiv.toEquiv.subtypeEquiv fun m => by
    change Q m = 0 ↔ Q' (e m) = 0
    rw [e.map_app])

theorem card_zeros_qForm : (Finset.univ.filter fun w => qForm w = 0).card = 120 := by
  simp only [qForm_apply]
  exact card_qPoly_zero

end CFSG.Monster.B.TwoA.Sp8
