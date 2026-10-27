
module

public import CFSG.Monster.B.TwoA.Sp8.QuadCosetBase
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
public import CFSG.Monster.B.TwoA.Sp8.GenActionHomBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA

theorem eq_zero_of_qPoly_add {t : V8} (h : ∀ w, qPoly (t + w) = qPoly w) : t = 0 := by
  have hqt : qPoly t = 0 := by
    have h0 := h 0
    rwa [add_zero, qPoly_zero] at h0
  exact nondegenerate_b0.1 t fun v => by rw [b0_eq_qPoly, h v, hqt, sub_zero, sub_self]

theorem orthogonalGroup_le_isometryGroup :
    TauCeti.QuadraticMap.orthogonalGroup qForm ≤ TauCeti.BilinForm.isometryGroup b0 := by
  intro M hM
  have hM' := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hM
  rw [TauCeti.BilinForm.mem_isometryGroup_iff]
  intro x y
  rw [← polarBilin_qForm, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar, QuadraticMap.polar, ← map_add, hM' (x + y), hM' x, hM' y]

@[expose] def orthMinusEquiv : TauCeti.QuadraticMap.orthogonalGroup qForm ≃*
    TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadMinus 4 (ZMod 2) 1 1) :=
  TauCeti.QuadraticMap.orthogonalGroupCongr isometryEquivQuadMinus

end CFSG.Monster.B.TwoA.Sp8
