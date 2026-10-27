module

public import CFSG.Sporadic.J4.QTNative
public import CFSG.Sporadic.J4.QT2AData

public section

namespace CFSG.Sporadic.J4.QT2A

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT

@[expose] def g5Mats (_ : Unit) : Array (Array V2) := locMats () ++ baseMats

@[expose] def g5Invs (_ : Unit) : Array (Array V2) := locInvs () ++ baseInvs

@[expose] def wR (w : List Int) : Array V2 := wordRows (g5Mats ()) (g5Invs ()) w

@[expose] def etaE (c : Nat) : Array V2 := etaRows (uTab (locMats ()) (locInvs ())) 11 c

@[expose] def zR (_ : Unit) : Array V2 := etaE 1131

@[expose] def addRows (X Y : Array V2) : Array V2 :=
  Array.ofFn (n := 112) fun i => (X[i.val]?.getD V2.zero).xor (Y[i.val]?.getD V2.zero)

@[expose] def phiR (_ : Unit) : Array V2 := addRows (zR ()) idRows

@[expose] def bRows (_ : Unit) : Array V2 :=
  Array.ofFn (n := 112) fun i =>
    if i.val < 50 then (phiR ())[kIdx[i.val]!]!
    else if i.val < 62 then compV[i.val - 50]! else idRows[kIdx[i.val - 62]!]!

@[expose] def patRows : Array V2 :=
  Array.ofFn (n := 112) fun i => if 62 ≤ i.val then idRows[i.val - 62]! else V2.zero

@[expose] def chkMod : Bool :=
  kIdx.size == 50 && compV.size == 12 && kIdx.all (fun k => k < 112) &&
    eqRows (mulRows (invRows (bRows ())) (bRows ())) idRows &&
    eqRows (mulRows (bRows ()) (mulRows (phiR ()) pRows)) patRows &&
    eqRows (mulRows pRows (invRows pRows)) idRows &&
    eqRows (mulRows (zR ()) (zR ())) idRows

@[expose] def inWB (x : V2) : Bool :=
  let y := frApply (frTable pRows) x
  (List.range 62).all fun t => !(y.testBit (50 + t))

@[expose] def cmz (X : Array V2) : Bool := eqRows (mulRows X (zR ())) (mulRows (zR ()) X)

@[expose] def trivOnComp (X : Array V2) : Bool :=
  let t := frTable X
  (List.range 12).all fun j => inWB ((frApply t (compV[j]!)).xor (compV[j]!))

@[expose] def inQz (X : Array V2) : Bool := cmz X && trivOnComp X

@[expose] def notQz (X : Array V2) : Bool := !trivOnComp X

@[expose] def wfR (X : Array V2) : Bool := X.size == 112 && X.all V2.wf

@[expose] def allDistinct : List (Array V2) → Bool
  | [] => true
  | x :: xs => xs.all (fun y => !eqRows x y) && allDistinct xs

@[expose] def invW (w : List Int) : List Int := w.reverse.map fun l => -l

@[expose] def cDw : List Int := invW aDw ++ invW bDw ++ aDw ++ bDw

@[expose] def yEl (n : Nat) : Array V2 :=
  mulRows (mulRows (powRows (wR aDw) (n / 9)) (powRows (wR bDw) ((n / 3) % 3)))
    (powRows (wR cDw) (n % 3))

@[expose] def chkY : Bool :=
  cmz (wR aDw) && cmz (wR bDw) && wfR (wR aDw) && wfR (wR bDw) &&
    eqRows (yEl 0) idRows &&
    (List.range 27).all (fun n => wfR (yEl n)) &&
    allDistinct ((List.range 27).map yEl) &&
    (List.range 27).all fun n =>
      (List.range 27).any (fun m => eqRows (mulRows (yEl n) (wR aDw)) (yEl m)) &&
        (List.range 27).any (fun m => eqRows (mulRows (yEl n) (wR bDw)) (yEl m))

@[expose] def y5R (_ : Unit) : Array V2 := powRows (wR y5w) y5e

@[expose] def y7R (_ : Unit) : Array V2 := powRows (wR y7w) y7e

@[expose] def y11R (_ : Unit) : Array V2 := powRows (wR y11w) y11e

@[expose] def chkYr (R : Array V2) (r : Nat) : Bool :=
  cmz R && wfR R && eqRows (powRows R r) idRows && !eqRows R idRows

@[expose] def qR (k : Nat) : Array V2 := wR (qGenW.getD k [])

@[expose] def chkQgens : Bool := qGenW.length == 12 && (List.range 12).all fun k => inQz (qR k)

@[expose] def chkNotQzY : Bool := (List.range 27).all fun n => n == 0 || notQz (yEl n)

@[expose] def chkNotQzPow (R : Array V2) (r : Nat) : Bool :=
  (List.range (r - 1)).all fun k => notQz (powRows R (k + 1))

@[expose] def nocomm (X Y : Array V2) : Bool := !eqRows (mulRows X Y) (mulRows Y X)

@[expose] def chkWit : Bool :=
  wfR (qR 0) && (List.range 27).all (fun n => n == 0 || nocomm (qR 0) (yEl n)) &&
    (List.range 4).all (fun k => nocomm (qR 0) (powRows (y5R ()) (k + 1))) &&
    (List.range 6).all (fun k => nocomm (qR 0) (powRows (y7R ()) (k + 1))) &&
    (List.range 10).all fun k => nocomm (qR 0) (powRows (y11R ()) (k + 1))

@[expose] def combMask (ms : List Nat) (t : Nat) : Nat :=
  (List.range ms.length).foldl (fun acc i => if t.testBit i then acc ^^^ ms.getD i 0 else acc) 0

@[expose] def conjE (c : Nat) (Y : Array V2) : Array V2 := mulRows (mulRows (etaE c) Y) (etaE c)

@[expose] def eConjOK (n : Nat) : Bool :=
  let ms := eMasks.getD n []
  let l := (List.range 64).map fun t => conjE (combMask ms t) (yEl n)
  ms.length == 6 && l.all wfR && allDistinct l

@[expose] def chkE : Bool := (List.range 27).all fun n => n == 0 || eConjOK n

@[expose] def qSub : List Nat := [2, 4, 5, 6, 9, 11]

@[expose] def qWord (t : Nat) : List Int :=
  (List.range 6).flatMap fun i => if t.testBit i then qGenW.getD (qSub.getD i 0) [] else []

@[expose] def chkQconj : Bool :=
  let ps := (List.range 64).map fun t => wR (qWord t)
  let pis := (List.range 64).map fun t => wR (invW (qWord t))
  ps.all wfR && (List.range 27).all fun n => n == 0 ||
    (let l := (List.zip ps pis).map fun p => mulRows (mulRows p.1 (yEl n)) p.2
     l.all wfR && allDistinct l)

@[expose] def chkLoc : Bool :=
  aDw.all (fun l => decide (l ∈ letters)) && bDw.all fun l => decide (l ∈ letters)

end CFSG.Sporadic.J4.QT2A
