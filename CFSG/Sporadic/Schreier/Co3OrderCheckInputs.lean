
module

public import CFSG.Sporadic.Schreier.Co3CertBase
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.Schreier.Co3CertBase
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.Schreier.Co3CertCheckBase
public import CFSG.Sporadic.Schreier.Co3CertCheckBase
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native

@[expose] def co3ChainBaseArr : Array Nat :=
  ((co3FinList 276 (by decide) co3ChainBase).map Fin.val).toArray

@[expose] def co3CoprimeBaseArr : Array Nat :=
  ((co3FinList 276 (by decide) co3CoprimeBase).map Fin.val).toArray

@[expose] def co3WordArr : Array Nat :=
  wordA 276 co3ChainArrs (rawInvs 276 co3ChainArrs) co3CoprimeWord

@[expose] def co3C1Arr : Array Nat :=
  compA 276 (compA 276 (invCand 276 co3WordArr) co3ChainArrs[1]!) co3WordArr

@[expose] def co3PowA (n : Nat) (t : Array Nat) : Nat → Array Nat
  | 0 => idA n
  | e + 1 => compA n t (co3PowA n t e)

end CFSG.Sporadic.Schreier.Co3
