module

public import Certificates.Data.CFSGNative.Co1.Odd

public section

namespace CFSG.Sporadic.Co1.CoTwoNative

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative

@[expose] def addRowsD (d : Nat) (X Y : Array Nat) : Array Nat :=
  Array.ofFn (n := d) fun i => (X[i.val]?.getD 0) ^^^ (Y[i.val]?.getD 0)

@[expose] def zeroRowsD (d : Nat) : Array Nat := Array.replicate d 0

@[expose] def wordRowsD (d : Nat) (G : Nat → Array Nat) (w : List Nat) : Array Nat :=
  w.foldl (fun acc l => mulRows d acc (G l)) (idRows d)

@[expose] def polyRowsD (d : Nat) (G : Nat → Array Nat) (theta : List (List Nat)) : Array Nat :=
  theta.foldl (fun acc w => addRowsD d acc (wordRowsD d G w)) (zeroRowsD d)

@[expose] def diagRowsD (d ℓ : Nat) : Array Nat :=
  Array.ofFn (n := d) fun i => if i.val = ℓ then 0 else 1 <<< i.val

def spinVecs (d : Nat) (act : Nat → Nat → Nat) (v0 : Nat) (par lab : Array Nat) : Array Nat :=
  (List.range d).foldl (fun L k => if k = 0 then L.push v0
    else L.push (act (lab[k]?.getD 0) (L[par[k]?.getD 0]?.getD 0))) #[]

@[expose] def spinCheck (d : Nat) (act : Nat → Nat → Nat) (v0 : Nat) (L par lab : Array Nat) :
    Bool :=
  (L[0]?.getD 0 == v0) && (List.range d).all fun k =>
    k == 0 || (decide (par[k]?.getD 0 < k) &&
      (L[k]?.getD 0 == act (lab[k]?.getD 0) (L[par[k]?.getD 0]?.getD 0)))

structure NortonCert where
  ell : Nat
  theta : List (List Nat)
  P : Array Nat
  Pinv : Array Nat
  Q : Array Nat
  Qinv : Array Nat
  v : Nat
  w : Nat
  parV : Array Nat
  labV : Array Nat
  Vinv : Array Nat
  parW : Array Nat
  labW : Array Nat
  Winv : Array Nat

@[expose] def nortonCheck (d : Nat) (G : Nat → Array Nat) (C : NortonCert) : Bool :=
  let actV : Nat → Nat → Nat := fun l x => vecMulN d (transposeRows d (G l)) x
  let actW : Nat → Nat → Nat := fun l x => vecMulN d (G l) x
  let LV := spinVecs d actV C.v C.parV C.labV
  let LW := spinVecs d actW C.w C.parW C.labW
  decide (C.ell < d) && mulRows d C.P C.Pinv == idRows d && mulRows d C.Q C.Qinv == idRows d &&
    mulRows d (mulRows d C.Q (polyRowsD d G C.theta)) C.P == diagRowsD d C.ell &&
    C.v == vecMulN d (transposeRows d C.P) (1 <<< C.ell) && C.w == (C.Q[C.ell]?.getD 0) &&
    spinCheck d actV C.v LV C.parV C.labV && mulRows d C.Vinv (transposeRows d LV) == idRows d &&
    spinCheck d actW C.w LW C.parW C.labW && mulRows d C.Winv (transposeRows d LW) == idRows d

@[expose] def perpCheck (n : Nat) (Ft Wr : Array Nat) (x : Nat) : Bool :=
  (List.range n).all fun j => !bilN Ft (Wr[j]?.getD 0) x

@[expose] def liftCheck (n d : Nat) (R Wr Mt : Array Nat) : Bool :=
  (List.range n).all fun j =>
    vecMulN d (transposeRows d R) (Wr[j]?.getD 0) == vecMulN n Wr (Mt[j]?.getD 0)

@[expose] def repCheck (Qt Ft R1 R2 Wr Mt1 Mt2 : Array Nat) (x1 x2 : Nat) : Bool :=
  isFixedN (transposeRows 24 R1) x1 && isFixedN (transposeRows 24 R1) x2 &&
    isFixedN (transposeRows 24 R2) x1 && isFixedN (transposeRows 24 R2) x2 &&
    perpCheck 22 Ft Wr x1 && perpCheck 22 Ft Wr x2 &&
    liftCheck 22 24 R1 Wr Mt1 && liftCheck 22 24 R2 Wr Mt2 &&
    decide ((Wr[0]?.getD 0) < 2 ^ 24) && !isFixedN (transposeRows 24 R1) (Wr[0]?.getD 0) &&
    bilN Ft (Wr[0]?.getD 0) (Wr[21]?.getD 0) && q0N Qt (x1 ^^^ x2)

end CFSG.Sporadic.Co1.CoTwoNative
