
module

public import CFSG.Monster.B.TwoA.Co2Inv.RowsBase
public import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Co2Inv.Data
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Census.PermBFS
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
public import CFSG.Monster.B.Co2.MatrixCertBase
public import CFSG.Monster.B.Co2.MatrixIsoBase
public import CFSG.Monster.B.Co2.Order
public import CFSG.Monster.B.Co2.SimpleBase
public import CFSG.Monster.B.Short.Faithful22
public import CFSG.Monster.B.Short.ParityCentralizer
public import CFSG.Monster.B.TwoA.Base.WCls
public import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.B.TwoA.Co2Inv.Data
public meta import CFSG.Monster.Code.Weights

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Co2Inv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census

@[expose] def actFrame (k c : ℕ) : ℕ := Native.actD 22 (cRows k) c

@[expose] def validW (c : ℕ) : Bool := decide (c < 2 ^ 22)

@[expose] def frameCert : NatCert := natBfs actFrame 21 31 200

@[expose] def frameCheck : Bool :=
  natCertOK actFrame 21 validW 31 frameCert && frameCert.pts == frameOrbit

attribute [local instance] wLeftAction

@[expose] def fCert : TreeCert := bfsCert amul fPerms idArr 20000

@[expose] def fixJ (a : Array ℕ) : Bool := (List.range 8).all fun j => a[j]! == j

@[expose] def fCheck : Bool :=
  certOK amul fPerms idArr fCert && fCert.pts.size == 11520 &&
    ((fCert.pts.toList.filter fixJ).map akey).mergeSort (fun a b => decide (a ≤ b)) ==
      (octPerms.toList.map akey).mergeSort (fun a b => decide (a ≤ b))

end CFSG.Monster.B.TwoA.Co2Inv
