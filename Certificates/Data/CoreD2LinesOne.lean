module

public import Certificates.Data.CoreD2Lines

public section

namespace Certificates.CoreD2Perm

open CFSG.PSL3Four.Native
open Certificates.FusD2Perm (powT wordT)

@[expose] def letterOfChar (c : Char) : Int :=
  if 'a' ≤ c ∧ c ≤ 'z' then ((c.toNat - 'a'.toNat + 1 : Nat) : Int)
  else if 'A' ≤ c ∧ c ≤ 'Z' then -((c.toNat - 'A'.toNat + 1 : Nat) : Int) else 0

@[expose] def wordsOfString (s : String) : List (List Int) :=
  ((s.splitOn ",").filter (· ≠ "")).map fun w => w.toList.map letterOfChar

@[expose] def allowedOne (V : VData) (i j : Nat) : Bool :=
  let f := V.gk.getD j default
  f.idx == i || (!(f.kind == 0) && f.f2 == 0)

@[expose] def wordOKOne (V : VData) (i : Nat) (w : List Int) : Bool :=
  w.all fun l => allowedOne V i (l.natAbs - 1)

@[expose] def expOK (V : VData) : Bool :=
  (eEnum V.base).tabs.all fun t => powT V.base.n t V.base.p == idTab V.base.n

@[expose] def checkVOne (V : VData) : Bool :=
  checkV V && expOK V &&
    allBelow V.ys.length fun i =>
      wordOKOne V i (V.wAs.getD i []) && wordOKOne V i (V.wBs.getD i [])

end Certificates.CoreD2Perm
