
module

public import CFSG.Sporadic.HNOddCore.CCheckBase
public import CFSG.Sporadic.HNOddCore.InvArrays
public import Certificates.Data.CFSGNative.ONSchreier.Tools
public meta import CFSG.Sporadic.HNOddCore.CCheckBase
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import Certificates.Data.CFSGNative.ONSchreier.Tools

public section

namespace CFSG.Sporadic.HNOddCore.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.F5.Native

@[expose] def progRun (n : Nat) :
    Array (Array Nat) → List (Bool × Nat × Nat × Nat) → Array (Array Nat) × Bool
  | regs, [] => (regs, true)
  | regs, (true, a, b, c) :: rest => progRun n (regs.set! c (pcomp n regs[a]! regs[b]!)) rest
  | regs, (false, a, b, _) :: rest =>
    let r := progRun n (regs.set! b (pinvCand n regs[a]!)) rest
    (r.1, pisInv n regs[a]! (pinvCand n regs[a]!) && r.2)

@[expose] def cTab (n : Nat) (a0 a1 : Array Nat) (hS : Array (Array Nat)) : Array Nat :=
  let k := pcomp n (pword n hS (pinvs n hS) LocalData.innerWord)
    (pinvCand n (seedWordArr n a0 a1 LocalData.outerWord))
  let W := ppow n (pcomp n a0 (pcomp n a1 a1)) 8
  let cAB := conjTabs n a0 a1 k (pinvCand n k) W (pinvCand n W)
  cRecArr n (bfsPar n a0 a1) cAB.1 cAB.2

@[expose] def restrictOK (T F pos s : Array Nat) : Bool := peq F.size (restrictTab T F pos) s

@[noinline, expose] def row1OK (n : Nat) (hS hSi : Array (Array Nat)) (c pos : Array Nat) : Bool :=
  fixListOK n c InvData.f1Arr.toList && pointsOK n InvData.f1Arr pos &&
    InvData.s1Perms.size == 9 && InvData.c1Words.size == 9 &&
    allBelowN 9 fun j => restrictOK (pword n hS hSi InvData.c1Words[j]!) InvData.f1Arr pos
      InvData.s1Perms[j]!

@[noinline, expose] def row4OK (n : Nat) (hS hSi : Array (Array Nat)) (c t x pos : Array Nat) :
    Bool :=
  fixListOK n t InvData.f4Arr.toList && pointsOK n InvData.f4Arr pos &&
    InvData.s4Perms.size == 11 && InvData.c4Words.size == 9 &&
    (allBelowN 9 fun j => restrictOK (pword n hS hSi InvData.c4Words[j]!) InvData.f4Arr pos
      InvData.s4Perms[j]!) &&
    restrictOK x InvData.f4Arr pos InvData.s4Perms[9]! &&
    restrictOK c InvData.f4Arr pos InvData.s4Perms[10]! && peq n (pcomp n x t) (pcomp n t x)

@[noinline, expose] def row6OK (n : Nat) (a0 : Array Nat) (hS hSi : Array (Array Nat))
    (e1 e2 pos : Array Nat) : Bool :=
  fixListOK n a0 InvData.f6Arr.toList && pointsOK n InvData.f6Arr pos &&
    InvData.s6Perms.size == 12 && InvData.c6Words.size == 10 &&
    (allBelowN 10 fun j => restrictOK (pword n hS hSi InvData.c6Words[j]!) InvData.f6Arr pos
      InvData.s6Perms[j]!) &&
    restrictOK e1 InvData.f6Arr pos InvData.s6Perms[10]! &&
    restrictOK e2 InvData.f6Arr pos InvData.s6Perms[11]! &&
    peq n (pcomp n e1 a0) (pcomp n a0 e1) && peq n (pcomp n e2 a0) (pcomp n a0 e2)

@[noinline, expose] def row6Run (n : Nat) (a0 : Array Nat) (hS hSi : Array (Array Nat))
    (r : Array (Array Nat) × Bool) (g : Array Nat) : Bool :=
  r.2 && pisInv n g (pinvCand n g) &&
    row6OK n a0 hS hSi (pcomp n (pinvCand n g) (pcomp n r.1[1]! g))
      (pcomp n (pinvCand n g) (pcomp n r.1[2]! g)) (posArr n InvData.f6Arr)

@[noinline, expose] def row2OK (n : Nat) (hS hSi : Array (Array Nat)) (t : Array Nat) : Bool :=
  fixCount n t == 8800 && InvData.a8Words.size == 6 &&
    fixedSet n (#[t] ++ InvData.a8Words.map (pword n hS hSi)) == [0]

@[noinline, expose] def xChecksH (n : Nat) (a0 a1 : Array Nat) (hS : Array (Array Nat))
    (c : Array Nat) : Bool :=
  row1OK n hS (pinvs n hS) c (posArr n InvData.f1Arr) &&
    row4OK n hS (pinvs n hS) c (pword n hS (pinvs n hS) InvData.t4Word)
      (pcomp n (seedWordArr n a0 a1 InvData.x4Root) (pword n hS (pinvs n hS) InvData.x4H))
      (posArr n InvData.f4Arr) &&
    row6Run n a0 hS (pinvs n hS) (progRun n (initRegs n a0 a1) InvData.m2Prog)
      (pcomp n (seedWordArr n a0 a1 InvData.m2ConjRoot)
        (pword n hS (pinvs n hS) InvData.m2ConjH)) &&
    row2OK n hS (pinvs n hS) (pword n hS (pinvs n hS) InvData.t2Word)

@[noinline, expose] def xChecksS (n : Nat) (a0 a1 : Array Nat) (hS : Array (Array Nat)) : Bool :=
  xChecksH n a0 a1 hS (cTab n a0 a1 hS)

@[noinline, expose] def xChecksR (n : Nat) (a0 a1 : Array Nat) (regs : Array (Array Nat)) : Bool :=
  xChecksS n a0 a1 (extendStrong n #[regs[1]!, regs[2]!] LocalData.strongWords)

@[noinline, expose] def xChecksO (O : VOrbit) : Bool :=
  xChecksR hnsData.n (natTab O.alpha) (natTab O.beta)
    (progRegs hnsData.n (initRegs hnsData.n (natTab O.alpha) (natTab O.beta)) Data.subgroupProgram)

end CFSG.Sporadic.HNOddCore.Native
