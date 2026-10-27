
module

public import CFSG.Monster.B.TwoA.Sp8.QuadForm
public import CFSG.Monster.B.TwoA.Census.PermClasses

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.Rep4371

theorem qPoly_zero : qPoly 0 = 0 := by decide

theorem b0_eq_qPoly (t v : Fin 8 → ZMod 2) : b0 t v = qPoly (t + v) - qPoly t - qPoly v := by
  rw [← polarBilin_qForm, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, qForm_apply,
    qForm_apply, qForm_apply]

end CFSG.Monster.B.TwoA.Sp8
