module

public import CFSG.Monster.B.CTIB.HInnerCert
public import Certificates.Data.CFSGNative.CTIB.Coset
public meta import CFSG.Monster.B.CTIB.HInnerCert
public meta import Certificates.Data.CFSGNative.CTIB.Coset

public section

namespace CFSG.Monster.B.GSide

open CFSG.Monster.B.CTIB CFSG.Monster.B.CTIB.Native CFSG.Monster.B.Max2.Native

@[expose] def cosetSqOK (t : Array Nat) : Bool :=
  [6, 8, 10].all fun k =>
    let A := (liftImgsN k).toArray
    let w := sqCode k
    Nat.all (2 ^ 23) fun n _ => innerTy t (qmul gArr w (qmul gArr (autApply gArr A n) n)) != 1

@[expose] def fusionWitnessOK (t : Array Nat) : Bool :=
  let A := (liftImgsN 8).toArray
  innerTy t 128 == 1 && autApply gArr A 128 == 128 &&
  qmul gArr 128 2 == qmul gArr 2 128 && qmul gArr 128 35 == qmul gArr 35 128 &&
  qmul gArr (sqCode 8) (qmul gArr (autApply gArr A 2) 2) == 1270988 &&
  qmul gArr (sqCode 8) (qmul gArr (autApply gArr A 35) 35) == 1255411 &&
  qmul gArr 1270988 128 == qmul gArr 128 1270988 &&
  qmul gArr 1255411 128 == qmul gArr 128 1255411 &&
  innerTy t 1270988 == 2 && innerTy t (qmul gArr 128 1270988) == 3 &&
  innerTy t 1255411 == 3 && innerTy t (qmul gArr 128 1255411) == 2 &&
  qmul gArr 34 1 == qmul gArr 1 34 && qmul gArr 34 34 == 2 ^ 22

end CFSG.Monster.B.GSide
