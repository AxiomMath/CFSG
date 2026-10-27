
module

public import CFSG.Sporadic.HNOddCore.XCheckBase
public import CFSG.Sporadic.HNOddCore.PCheckBase
public meta import CFSG.Sporadic.HNOddCore.XCheckBase
public meta import CFSG.Sporadic.HNOddCore.PCheckBase

public section

namespace CFSG.Sporadic.HNOddCore.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.F5.Native

@[expose] def evalWordPt (T Ti : Array (Array Nat)) : List Int → Nat → Nat
  | [], p => p
  | l :: w, p =>
    let q := evalWordPt T Ti w p
    if 0 < l then (T[l.toNat - 1]!)[q]! else (Ti[(-l).toNat - 1]!)[q]!

@[expose] def evalLiftF (T Ti : Array (Array Nat)) (par : Array (List Int)) :
    Nat → Nat → Nat → Nat
  | 0, _, p => p
  | f + 1, r, p =>
    if r = 0 then p
    else evalWordPt T Ti pWords[plabOf par r]! (evalLiftF T Ti par f (pparOf par r) p)

@[expose] def evalLift (T Ti : Array (Array Nat)) (par : Array (List Int)) (r p : Nat) : Nat :=
  evalLiftF T Ti par r r p

@[noinline, expose] def liftChecksT (n : Nat) (T Ti : Array (Array Nat)) (t : Array Nat)
    (par : Array (List Int)) : Bool :=
  T.size == 11 && Ti.size == 11 && (allBelowN 11 fun j => pisInv n T[j]! Ti[j]!) &&
    InvData.witRep.size == 39 && InvData.witKer.size == 39 && InvData.witFix.size == 39 &&
    (allBelowN 39 fun w => decide (InvData.witFix[w]! < n) &&
      evalLift T Ti par InvData.witRep[w]!
        (if InvData.witKer[w]! = 1 then t[InvData.witFix[w]!]! else InvData.witFix[w]!) ==
        InvData.witFix[w]!) &&
    (allBelowN InvData.nonRep.size fun i => !(allBelowN n fun p =>
      evalLift T Ti par InvData.nonRep[i]! (evalLift T Ti par InvData.nonRep[i]! p) == p)) &&
    (allBelowN 29 fun c => InvData.nonRep.contains pReps[c]! || !(allBelowN n fun p =>
      t[p]! == p || evalLift T Ti par pReps[c]! (evalLift T Ti par pReps[c]! p) != p))

@[expose] def genTabs (n : Nat) (a0 a1 : Array Nat) (hS : Array (Array Nat)) (c : Array Nat) :
    Array (Array Nat) :=
  ((InvData.c4Words.extract 0 9).map (pword n hS (pinvs n hS))).push
      (pcomp n (seedWordArr n a0 a1 InvData.x4Root) (pword n hS (pinvs n hS) InvData.x4H)) |>.push c

@[noinline, expose] def liftChecksH (n : Nat) (a0 a1 : Array Nat) (hS : Array (Array Nat))
    (c : Array Nat) : Bool :=
  let T := genTabs n a0 a1 hS c
  liftChecksT n T (pinvs n T) (pword n hS (pinvs n hS) InvData.t4Word) InvData.parRecs

@[noinline, expose] def liftChecksS (n : Nat) (a0 a1 : Array Nat) (hS : Array (Array Nat)) :
    Bool :=
  liftChecksH n a0 a1 hS (cTab n a0 a1 hS)

@[noinline, expose] def liftChecksR (n : Nat) (a0 a1 : Array Nat) (regs : Array (Array Nat)) :
    Bool :=
  liftChecksS n a0 a1 (extendStrong n #[regs[1]!, regs[2]!] LocalData.strongWords)

@[noinline, expose] def liftChecksO (O : VOrbit) : Bool :=
  liftChecksR hnsData.n (natTab O.alpha) (natTab O.beta)
    (progRegs hnsData.n (initRegs hnsData.n (natTab O.alpha) (natTab O.beta)) Data.subgroupProgram)

end CFSG.Sporadic.HNOddCore.Native
