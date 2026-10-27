module

public import CFSG.Sporadic.J4.QT2LocX0Native
public import CFSG.Sporadic.J4.QT2LocX0KData
public import CFSG.Sporadic.J4.QT2LocNative

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A

@[expose] def x0Q1 : V2 := ⟨UInt64.ofNat x0Q1Lo, UInt64.ofNat x0Q1Hi⟩

@[expose] def kWords : List (List Int) := kStrings.map w5

@[expose] def kGenRows : Array (Array V2) := (kWords.map wR).toArray

@[expose] def kInvRows : Array (Array V2) := kGenRows.map invRows

@[expose] def kAllRows : Array (Array V2) := kGenRows ++ kInvRows

@[inline, expose] def kStep (M : Array V2) (g : Nat) : Array V2 := mulRows M (kAllRows[g]!)

@[expose] def kOrb : MOrb := obfs kStep 12 idRows 15360 15

@[expose] def chkKGens : Bool :=
  kWords.length == 6 && kGenRows.size == 6 && kInvRows.size == 6 &&
    kWords.all (fun w => w.all fun l => letters.contains l) &&
    (List.range 6).all (fun i =>
      wfRows kGenRows[i]! && wfRows kInvRows[i]! &&
        eqRows (mulRows kGenRows[i]! kInvRows[i]!) idRows &&
        eqRows (mulRows kInvRows[i]! kGenRows[i]!) idRows &&
        (frApply (frTable kGenRows[i]!) x0Q1).beq x0Q1) &&
    x0Pts.contains x0Q1 && differs x0Q1 rootV

@[expose] def chkKOrb : Bool := oOrbOK kStep 12 idRows kOrb 15360

@[expose] def chkKComm : Bool :=
  (kOrb.mats.toList.filter fun M =>
    eqRows (mulRows M (x0GenRows[0]!)) (mulRows (x0GenRows[0]!) M)).length == 40

@[expose] def eFixMasks (T : Array (Array V2)) (v : V2) : List Nat :=
  (List.range 2048).filter fun c => !differs (frApply (frTable (etaRows T 11 c)) v) v

@[expose] def chkEStab : Bool :=
  let T := uTab (locMats ()) (locInvs ())
  (eFixMasks T x0Q1).length == 2 &&
    (List.range 7).all fun l =>
      (eFixMasks T (pathVec (repPaths.getD l []))).length == [2048, 2, 1, 1, 16, 512, 128].getD l 0

@[expose] def chkKAll : Bool := chkKGens && chkKOrb && chkKComm && chkEStab

end CFSG.Sporadic.J4.QT2
