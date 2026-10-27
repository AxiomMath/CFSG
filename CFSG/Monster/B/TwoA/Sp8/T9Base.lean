
module

public import CFSG.Monster.B.TwoA.Sp8.ElemAbBase
public import CFSG.Monster.B.TwoA.Sp8.QuadDataBase
public meta import CFSG.Monster.B.Rep4371.Model
public meta import CFSG.Monster.B.TwoA.Sp8.LiftsBase
public import CFSG.Monster.B.TwoA.Sp8.LiftsBase
public import CFSG.Monster.B.TwoA.Sp8.LiftsInputs
public import CFSG.Monster.B.TwoA.Sp8.A8Inputs
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Base.WCls
public import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.B.TwoA.Co2Inv.Data
public import CFSG.Monster.B.TwoA.Co2Inv.RowsInputs
public import CFSG.Monster.B.TwoA.Base.RankThreeParBase
public import CFSG.Monster.B.TwoA.Sp8.ZrelBase
public import CFSG.Monster.Visible.SignCompat.TrialityCycleOctad

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371
  CFSG.Monster.B.TwoA.Census

@[expose] def cP : Q := pauliQ (false, 0, 127)

theorem cP_eq_rMinus : cP = rMinus 0 2 := pauliQ_cocode (w := 5) (by decide) (by decide)

@[expose] def initV (v : Fin 9 → ZMod 2) : Fin 8 → ZMod 2 := fun k => v k.castSucc

theorem initV_single_castSucc (j : Fin 8) (a : ZMod 2) :
    initV (Pi.single j.castSucc a) = Pi.single j a := by
  funext k
  by_cases h : k = j
  · subst h
    simp [initV]
  · rw [initV, Pi.single_eq_of_ne (fun e => h (Fin.castSucc_injective _ e)),
      Pi.single_eq_of_ne h]

theorem initV_single_last (a : ZMod 2) : initV (Pi.single (Fin.last 8) a) = 0 := by
  funext k
  rw [initV, Pi.single_eq_of_ne (Fin.castSucc_lt_last k).ne, Pi.zero_apply]

@[expose] def extV (w : Fin 8 → ZMod 2) : Fin 9 → ZMod 2 := Fin.snoc (α := fun _ => ZMod 2) w 0

theorem initV_extV (w : Fin 8 → ZMod 2) : initV (extV w) = w := by
  funext k
  rw [initV, extV, Fin.snoc_castSucc]

end CFSG.Monster.B.TwoA.Sp8
