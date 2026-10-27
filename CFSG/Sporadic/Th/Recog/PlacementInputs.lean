module

public import CFSG.Sporadic.Th.Recog.JLettersInputs
public import Certificates.Data.Th687.PlaceWords

public section

namespace CFSG.Sporadic.Th.Recog.Place

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3

structure Base where
  H : Array (Array V4)
  HI : Array (Array V4)
  L : Array (Array V4)
  LI : Array (Array V4)
  h : Array (Array V4)
  hI : Array (Array V4)
  W : Array (Array V4)
  WI : Array (Array V4)
  V : Array (Array V4)
  VI : Array (Array V4)
  R : Array (Array (Array V4))
  Z : Array (Array (Array V4))
  A : Array V4
  D : Array V4
  DI : Array V4

@[expose] def get1 (T : Array (Array V4)) (i : ℕ) : Array V4 := (T[i]?).getD idRows

@[expose] def get2 (T : Array (Array (Array V4))) (i m : ℕ) : Array V4 :=
  ((T[i]?).getD #[])[m]?.getD idRows

@[expose] def Base.make (H HI : Array (Array V4)) : Base :=
  let L := Array.ofFn (n := 6) fun i => wRowsArr H HI (lWord i)
  let LI := Array.ofFn (n := 6) fun i => wRowsArr H HI (FreeGroup.invRev (lWord i))
  let h := Array.ofFn (n := 5) fun j => wRowsArr L LI (hWord j)
  let hI := Array.ofFn (n := 5) fun j => wRowsArr L LI (FreeGroup.invRev (hWord j))
  let W := Array.ofFn (n := 2) fun i => wRowsArr L LI (wpWord i)
  let R := Array.ofFn (n := 2) fun i => Array.ofFn (n := 8) fun m => wRowsArr h hI (repWord i m)
  { H := H
    HI := HI
    L := L
    LI := LI
    h := h
    hI := hI
    W := W
    WI := Array.ofFn (n := 2) fun i => wRowsArr L LI (FreeGroup.invRev (wpWord i))
    V := Array.ofFn (n := 2) fun i => wRowsArr H HI (vWord i)
    VI := Array.ofFn (n := 2) fun i => wRowsArr H HI (FreeGroup.invRev (vWord i))
    R := R
    Z := Array.ofFn (n := 2) fun i => Array.ofFn (n := 8) fun m => mulRows (get1 W i) (get2 R i m)
    A := get1 H 0
    D := get1 H 3
    DI := get1 HI 3 }

@[expose] def vRows (B : Base) (i : Fin 2) : Array V4 := get1 B.V i

@[expose] def orbRows (B : Base) (i : Fin 2) (r : Fin 18) : Array V4 :=
  mulRows (mulRows (wRowsArr B.h B.hI (orbWord i r)) (vRows B i))
    (wRowsArr B.h B.hI (FreeGroup.invRev (orbWord i r)))

@[expose] def repRows (B : Base) (i : Fin 2) (m : Fin 8) : Array V4 := get2 B.R i m

@[expose] def fourRows (B : Base) (i : Fin 2) (u : Fin 4) : Array V4 :=
  match u with
  | 0 => idRows
  | 1 => B.A
  | 2 => vRows B i
  | 3 => mulRows B.A (vRows B i)

@[expose] def split32 (q : Fin 32) : Fin 8 × Fin 4 := (finProdFinEquiv (m := 8) (n := 4)).symm q

@[expose] def centRows (B : Base) (i : Fin 2) (q : Fin 32) : Array V4 :=
  mulRows (repRows B i (split32 q).1) (fourRows B i (split32 q).2)

@[expose] def zRows (B : Base) (i : Fin 2) (m : Fin 8) : Array V4 := get2 B.Z i m

@[expose] def zInvRows (B : Base) (i : Fin 2) (m : Fin 8) : Array V4 :=
  mulRows (wRowsArr B.h B.hI (FreeGroup.invRev (repWord i m))) (get1 B.WI i)

@[expose] def canon (X : Array V4) : Array V4 := transposeRows (transposeRows X)

@[expose] def ord8 (X : Array V4) : Bool :=
  let X2 := mulRows X X
  let X4 := mulRows X2 X2
  eqRows (mulRows X4 X4) idRows && !eqRows (canon X4) idRows

@[expose] def cubeNe (X : Array V4) : Bool :=
  !eqRows (canon (mulRows (mulRows X X) X)) idRows

@[expose] def checkA (B : Base) : Bool :=
  eqRows (wRowsArr B.h B.hI aHWord) B.A && eqRows (mulRows B.A B.A) idRows

@[expose] def checkV (B : Base) : Bool :=
  (List.finRange 2).all (fun i =>
    eqRows (mulRows (vRows B i) (vRows B i)) idRows &&
      eqRows (mulRows B.A (vRows B i)) (mulRows (vRows B i) B.A)) &&
    eqRows (mulRows (mulRows (vRows B 0) (vRows B 1)) (mulRows (vRows B 0) (vRows B 1))) B.A

@[expose] def checkH (B : Base) : Bool :=
  (List.finRange 5).all fun j =>
    eqRows (mulRows (get1 B.h j) B.A) (mulRows B.A (get1 B.h j))

@[expose] def checkOrb (B : Base) : Bool :=
  (List.finRange 2).all fun i => decide (List.ofFn fun r => canon (orbRows B i r)).Nodup

@[expose] def checkRep (B : Base) : Bool :=
  (List.finRange 2).all fun i => (List.finRange 8).all fun m =>
    eqRows (mulRows (repRows B i m) (vRows B i)) (mulRows (vRows B i) (repRows B i m))

@[expose] def checkCent (B : Base) : Bool :=
  (List.finRange 2).all fun i => decide (List.ofFn fun q => canon (centRows B i q)).Nodup

@[expose] def checkWp (B : Base) : Bool :=
  (List.finRange 2).all fun i =>
    eqRows (mulRows (mulRows (get1 B.W i) B.A) (get1 B.WI i)) (vRows B i) &&
      eqRows (mulRows (mulRows (get1 B.W i) (vRows B i)) (get1 B.WI i)) (mulRows B.A (vRows B i))

@[expose] def checkCoset (B : Base) : Bool :=
  (List.finRange 2).all fun i => (List.finRange 8).all fun m =>
    (good i).contains m ||
      (List.finRange 4).all (fun u => cubeNe (mulRows (zRows B i m) (fourRows B i u))) ||
      ord8 (mulRows (vRows B (1 - i)) (zRows B i m))

@[expose] def checkPair (B : Base) : Bool :=
  (good 0).all fun m₀ => (good 1).all fun m₁ =>
    pair 0 == (m₀, m₁) || pair 1 == (m₀, m₁) ||
      ord8 (mulRows (zRows B 0 m₀)
        (mulRows (mulRows B.D (mulRows (vRows B 0) (zRows B 1 m₁))) B.DI))

@[expose] def gensRows (B : Base) (x : Fin 2) : Array (Array V4) :=
  #[vRows B 0, vRows B 1, zRows B 0 (pair x).1, zRows B 1 (pair x).2]

@[expose] def gensInvRows (B : Base) (x : Fin 2) : Array (Array V4) :=
  #[get1 B.VI 0, get1 B.VI 1, zInvRows B 0 (pair x).1, zInvRows B 1 (pair x).2]

@[expose] def checkXw (B : Base) : Bool :=
  (List.finRange 2).all fun x =>
    let G := gensRows B x
    let GI := gensInvRows B x
    [Twist.id, .f1, .f3, .f13].all fun k => (List.finRange 2).all fun j =>
      eqRows (wRowsArr B.H B.HI (xw (k, x) j)) (wRowsArr G GI (xwExpr k x j))

@[expose] def check (_ : Unit := ()) : Bool :=
  let B := Base.make (rowsHswArr ()) (rowsHswInvArr ())
  checkA B && checkV B && checkH B && checkOrb B && checkRep B && checkCent B && checkWp B &&
    checkCoset B && checkPair B && checkXw B

end CFSG.Sporadic.Th.Recog.Place
