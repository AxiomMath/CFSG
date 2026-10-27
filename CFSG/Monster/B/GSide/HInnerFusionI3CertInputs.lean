module

public import CFSG.Monster.B.CTIB.HInnerCert
public import Certificates.Data.CFSGNative.CTIB.Coset
public meta import CFSG.Monster.B.CTIB.HInnerCert
public meta import Certificates.Data.CFSGNative.CTIB.Coset

public section

namespace CFSG.Monster.B.GSide

open CFSG.Monster.B.CTIB CFSG.Monster.B.CTIB.Native CFSG.Monster.B.Max2.Native

@[expose] def frameA (t : Array Nat) (n : Nat) : Bool :=
  innerTy t n == 1 && qmul gArr n 7 == qmul gArr 7 n && innerTy t (qmul gArr n 7) == 3

@[expose] def gA6 (_ : Unit) : Array (Array Nat) :=
  ((List.range 15).map fun j => wordAut (genInvImgs ()) (centWordN 6 j)).toArray

@[expose] def ds6 : Array Nat := ((List.range 15).map fun j => deltaN 6 j).toArray

@[expose] def fusePts6 (gA : Array (Array Nat)) (rep size : Nat) : Array Nat :=
  (natBfs (fuseAct (liftImgsN 6).toArray gA ds6) 37 rep (size + 1)).1

@[expose] def commR6 (t : Array Nat) (n : Nat) : Bool :=
  innerTy t n == 3 &&
    qmul gArr (autApply gArr (liftImgsN 6).toArray n) 10541 == qmul gArr 10541 n

@[expose] def eCodes : List Nat :=
  [4100, 260, 5, 269, 13, 4172, 13, 1, 5, 4172, 64, 4357, 321, 8, 4165]

@[expose] def fAct (gA : Array (Array Nat)) (j n : Nat) : Nat :=
  qmul gArr (qmul gArr (qinv (eCodes.getD j 0)) (autApply gArr (gA.getD j #[]) n))
    (eCodes.getD j 0)

@[expose] def fixR6 (gA : Array (Array Nat)) (j : Nat) : Bool :=
  qmul gArr (qinv (autApply gArr (liftImgsN 6).toArray (eCodes.getD j 0)))
    (qmul gArr (fuse gArr (gA.getD j #[]) (ds6.getD j 0) 10541) (eCodes.getD j 0)) == 10541

@[expose] def frameBOK (t : Array Nat) (gA : Array (Array Nat)) (L4 L8 : Array Nat) : Bool :=
  let c := natBfs (fAct gA) 15 854 30241
  (L4.toList.filter fun a => commR6 t (qmul gArr (qinv 10541) a)).length == 30240 &&
    L8.all (fun a => !commR6 t (qmul gArr (qinv 10541) a)) &&
    commR6 t 854 && L4.contains (qmul gArr 10541 854) &&
    (List.range 15).all (fixR6 gA) &&
    natCertOK (fAct gA) 15 (fun p => decide (p < 2 ^ 23)) 854 c.1 c.2.1 c.2.2.1 c.2.2.2 &&
    c.1.size == 30240

@[expose] def i3CertOK (t : Array Nat) : Bool :=
  let gA := gA6 ()
  countBelow (frameA t) (2 ^ 23) 0 == 2240 &&
    frameBOK t gA (fusePts6 gA 43 34560) (fusePts6 gA 46090 64)

end CFSG.Monster.B.GSide
