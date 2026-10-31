
module

public import CFSG.Monster.B.TwoA.Co2Inv.RowsBase
public import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Co2Inv.Data
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Census.PermBFS
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.TwoA.Co2Inv.FrameCertInputs
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

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Co2Inv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census

attribute [local instance] wLeftAction

theorem smul_def (k : Kstab v0) (x : Wv v0) : k • x = wAct v0 k⁻¹ x := rfl

theorem decW_inj_valid {a b : ℕ} (ha : validW a = true) (hb : validW b = true)
    (h : decW a = decW b) : a = b :=
  decW_injective (of_decide_eq_true ha) (of_decide_eq_true hb) h

theorem fPerms_size : fPerms.size = 9 := rfl

def F9 : Subgroup (Equiv.Perm (Fin 24)) :=
  Subgroup.closure ((fun k => decode fPerms[k]!) '' {k | k < fPerms.size})

end CFSG.Monster.B.TwoA.Co2Inv
