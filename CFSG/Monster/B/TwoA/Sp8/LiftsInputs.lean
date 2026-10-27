
module

public import CFSG.Monster.B.TwoA.Sp8.DataBase
public import CFSG.Monster.B.TwoA.Census.CentralSqrt
public meta import CFSG.Monster.B.Rep4371.Model
public import CFSG.Monster.B.Co2.IrredAllBase
public import CFSG.Monster.B.Co2.IrredBase
public import CFSG.Monster.B.Co2.IrredMainBase
public import CFSG.Monster.B.Co2.Simple
public import CFSG.Monster.B.TwoA.Base.EU
public import CFSG.Monster.B.TwoA.Co2Inv.CentOrderBase
public import CFSG.Monster.B.TwoA.Co2Inv.ConjCertBase
public import CFSG.Monster.B.TwoA.Co2Inv.FrameCertBase
public import CFSG.Monster.B.TwoA.Co2Inv.MrBase
public import CFSG.Monster.B.TwoA.Triality.PermLift
public import CFSG.Monster.Visible.Faithful

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371
  CFSG.Monster.B.TwoA.Census

@[expose] def liftP : Fin 8 → Model.Pauli :=
  ![(true, 0, 0), (false, 63, 0), (false, 0, 128), (false, 0, 124), (false, 0, 579),
    (false, 0, 323), (false, 3, 60), (false, 0, 191)]

@[expose] def foldP (v : Fin 8 → ZMod 2) : Model.Pauli :=
  (List.finRange 8).foldl (fun acc k => if v k = 1 then Model.Pauli.mul acc (liftP k) else acc)
    (false, 0, 0)

end CFSG.Monster.B.TwoA.Sp8
