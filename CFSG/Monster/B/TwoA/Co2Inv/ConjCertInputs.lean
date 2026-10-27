
module

public import CFSG.Monster.B.TwoA.Co2Inv.RowsBase
public import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Co2Inv.Data
public meta import CFSG.Monster.B.TwoA.Census.NatCert
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

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Co2Inv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census

@[expose] def rowOf (n t : ℕ) : ℕ := n / 2 ^ (22 * t) % 2 ^ 22

@[expose] def rowsOf (n : ℕ) : Array ℕ := ((List.range 22).map (rowOf n)).toArray

@[expose] def encL : List ℕ → ℕ
  | [] => 0
  | r :: l => r % 2 ^ 22 + 2 ^ 22 * encL l

@[expose] def invRows : Array (Array ℕ) :=
  ((List.range 24).map fun k => Native.invMat 22 (gRows k)).toArray

@[expose] def conjRowsL (k : ℕ) (T : Array ℕ) : List ℕ :=
  (List.range 22).map fun j => Native.actD 22 (gRows k) (Native.actD 22 T (invRows[k]!)[j]!)

@[expose] def actConj (k n : ℕ) : ℕ := encL (conjRowsL k (rowsOf n))

@[expose] def validConj (n : ℕ) : Bool := n == encL (rowsOf n).toList

@[expose] def rootConj : ℕ := encL (gRows 12).toList

@[expose] def conjCert : NatCert := natBfs actConj 24 rootConj 60000

@[expose] def conjCheck : Bool :=
  natCertOK actConj 24 validConj rootConj conjCert && conjCert.pts.size == 56925 &&
    (List.range 24).all (fun k => (List.range 22).all fun j =>
      Native.actD 22 (gRows k) ((invRows[k]!)[j]!) == 1 <<< j) &&
    (List.range 22).all (fun t => rowOf rootConj t == (gRows 12)[t]!)

end CFSG.Monster.B.TwoA.Co2Inv
