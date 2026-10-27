module

public import CFSG.Sporadic.HNOddCore.InvData
public import CFSG.Sporadic.HNSchreier.LocalCheck
public meta import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck

public section

namespace CFSG.Sporadic.HNOddCore.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native

@[expose] def cyc45 (i : Nat) : Array Nat :=
  Array.ofFn (n := 12) fun j => if j.val = 4 then 5 else if j.val = 5 then i else
    if j.val = i then 4 else j.val

@[expose] def nat2 : List Nat := [1, 0, 3, 2, 4, 5, 6, 7, 8, 9, 10, 11]

@[expose] def natOK (nS nSi : Array (Array Nat)) (w : List Int) (a : Array Nat) : Bool :=
  plettersOK 17 w && peq 12 (pword 12 nS nSi w) a

@[expose] def natAllOK (nS nSi : Array (Array Nat)) (W : Array (List Int)) (A : Array (List Nat)) :
    Bool :=
  W.size == A.size && allBelowN W.size fun j => natOK nS nSi W[j]! (natArr A[j]!)

@[noinline, expose] def natChecksS (nS : Array (Array Nat)) : Bool :=
  let nSi := pinvs 12 nS
  natOK nS nSi InvData.t2Word (natArr nat2) && natOK nS nSi InvData.t4Word (natArr InvData.nat4) &&
    natAllOK nS nSi InvData.c1Words InvData.c1Nat && InvData.c1Words.size == 9 &&
    natAllOK nS nSi InvData.c4Words InvData.c4Nat && InvData.c4Words.size == 9 &&
    natAllOK nS nSi InvData.c6Words InvData.c6Nat && InvData.c6Words.size == 10 &&
    InvData.a8Words.size == 6 &&
    allBelowN 6 fun j => natOK nS nSi InvData.a8Words[j]! (cyc45 (j + 6))

@[noinline, expose] def natChecks : Bool :=
  natChecksS (extendStrong 12 #[natArr LocalData.natGen1, natArr LocalData.natGen2]
    LocalData.strongWords)

@[expose] def commOK (a b : Array Nat) : Bool := peq 12 (pcomp 12 a b) (pcomp 12 b a)

@[noinline, expose] def natCommChecks : Bool :=
  (allBelowN InvData.c1Nat.size fun j =>
      commOK (natArr InvData.c1Nat[j]!) (natArr InvData.nat1)) &&
    (allBelowN InvData.c4Nat.size fun j =>
      commOK (natArr InvData.c4Nat[j]!) (natArr InvData.nat4)) &&
    (allBelowN InvData.c6Nat.size fun j =>
      commOK (natArr InvData.c6Nat[j]!) (natArr InvData.nat6)) &&
    commOK (natArr InvData.nat1) (natArr InvData.nat4)

end CFSG.Sporadic.HNOddCore.Native
