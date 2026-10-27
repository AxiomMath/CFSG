module

public import Certificates.Data.Kernel.J4Q.Mat
public import Certificates.Data.CFSGNative.J4ZCent.Check
public import CFSG.Certificates.Kernel.Common.F2Dot
public import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.KC.J4R0

open CFSG.KC.J4Q (mulJ vecJ getN wordJ)
open CFSG.KC.F2Dot (maskFrom xorL)
open CFSG.Sporadic.J4.ZCent (g0W rW tW)

variable (c rm one : Nat)

@[expose] noncomputable def wK (X : List Nat) (e : Nat) : Nat → Nat → Nat
  | _, 0 => one
  | k, m + 1 => bif e.testBit k then mulJ c rm (getN one X k) (wK X e (k + 1) m)
      else wK X e (k + 1) m

@[expose] noncomputable def zK (X : List Nat) (a : Nat) : Nat := wK c rm one X (a <<< 12) 12 3

@[expose] def ent (T : List (List Nat)) (k j : Nat) : Nat := (T.getD k []).getD j 0

@[expose] noncomputable def relOK (X : List Nat) (CT : List (List Nat)) (SQ : List Nat) : Bool :=
  (List.range 12).all (fun k => (List.range 12).all fun j =>
    !decide (k < j) || (Nat.blt (ent CT k j) 8 &&
      Nat.beq (mulJ c rm (getN one X k) (getN one X j))
        (mulJ c rm (mulJ c rm (getN one X j) (zK c rm one X (ent CT k j))) (getN one X k)))) &&
  (List.range 12).all (fun k => Nat.blt (SQ.getD k 0) 8 &&
    Nat.beq (mulJ c rm (getN one X k) (getN one X k)) (zK c rm one X (SQ.getD k 0))) &&
  [12, 13, 14].all fun i => Nat.beq (mulJ c rm (getN one X i) (getN one X i)) one &&
    (List.range 15).all fun j =>
      Nat.beq (mulJ c rm (getN one X i) (getN one X j)) (mulJ c rm (getN one X j) (getN one X i))

@[expose] def memN (p : Nat) (O : List Nat) : Bool := O.any (Nat.beq p)

@[expose] noncomputable def sep1 (X : List Nat) (k : Nat) (O : List Nat) : Bool :=
  !O.isEmpty && O.all (fun o => Nat.blt o (2 ^ 112)) &&
    O.all (fun o => (List.range 15).all fun j =>
      !decide (k < j) || memN (vecJ rm o (getN one X j)) O) &&
    !memN (vecJ rm (O.headD 0) (getN one X k)) O

@[expose] noncomputable def sepOK (X : List Nat) (SEP : List (List Nat)) : Bool :=
  (List.range 15).all fun k => sep1 rm one X k (SEP.getD k [])

@[expose] def csym (CT : List (List Nat)) (k j : Nat) : Nat :=
  if k < 12 ∧ j < 12 then (if k < j then ent CT k j else if j < k then ent CT j k else 0) else 0

@[expose] def colK (CT : List (List Nat)) (q : Nat) : Nat :=
  maskFrom (fun k => (csym CT k (q / 3)).testBit (q % 3)) 0 15

@[expose] def radOK (CT : List (List Nat)) (RL : List (List Nat)) : Bool :=
  (List.range 12).all fun p => (RL.getD p []).all (fun q => Nat.blt q 36) &&
    Nat.beq (xorL ((RL.getD p []).map (colK CT))) (2 ^ p)

@[expose] noncomputable def normOK (X : List Nat) (g : Nat) (N : List Nat) : Bool :=
  (List.range 15).all fun j =>
    Nat.beq (mulJ c rm g (getN one X j)) (mulJ c rm (wK c rm one X (N.getD j 0) 0 15) g)

@[expose] noncomputable def coverOK (X T : List Nat) (g : Nat) (CV : List (Nat × Nat)) : Bool :=
  (List.range 60).all fun i => Nat.blt (CV.getD i (0, 0)).1 60 &&
    Nat.beq (mulJ c rm (getN one T i) g)
      (mulJ c rm (getN one T (CV.getD i (0, 0)).1) (wK c rm one X (CV.getD i (0, 0)).2 0 15))

@[expose] noncomputable def posW (a b : Nat) (u : List Nat) : Nat :=
  u.foldl (fun acc l => mulJ c rm acc (bif Nat.beq l 0 then a else b)) one

@[expose] noncomputable def gwOK (X B : List Nat) (a b : Nat) (GW : List (List Nat × Nat)) : Bool :=
  (List.range 16).all fun j => (GW.getD j ([], 0)).1.all (fun l => Nat.blt l 2) &&
    Nat.beq (getN one B j)
      (mulJ c rm (posW c rm one a b (GW.getD j ([], 0)).1) (wK c rm one X (GW.getD j ([], 0)).2 0 15))

@[expose] noncomputable def zbOK (X B : List Nat) : Bool :=
  [12, 13, 14].all fun i => (List.range 16).all fun j =>
    Nat.beq (mulJ c rm (getN one X i) (getN one B j)) (mulJ c rm (getN one B j) (getN one X i))

@[expose] noncomputable def xw (B INV X : List Nat) (k : Nat) : Nat :=
  bif Nat.blt k 12 || Nat.beq k 14 then wordJ c rm one B INV (rW.getD k [])
  else bif Nat.beq k 12 then mulJ c rm (getN one X 11) (wordJ c rm one B INV (rW.getD 12 []))
  else mulJ c rm (getN one X 11) (wordJ c rm one B INV (rW.getD 13 []))

@[expose] noncomputable def baseOK (GL B X T : List Nat) (B3I B4I : Nat) : Bool :=
  (List.range 16).all (fun i => Nat.beq (getN one B i) (wordJ c rm one GL [] (g0W.getD i []))) &&
  Nat.beq B3I (mulJ c rm (mulJ c rm (getN one B 3) (getN one B 3)) (getN one B 3)) &&
  Nat.beq (mulJ c rm (getN one B 3) B3I) one &&
  Nat.beq B4I (mulJ c rm (getN one B 4) (getN one B 4)) &&
  Nat.beq (mulJ c rm (getN one B 4) B4I) one &&
  (List.range 15).all (fun k => Nat.beq (getN one X k) (xw c rm one B [one, one, one, B3I, B4I] X k)) &&
  (List.range 60).all fun i =>
    Nat.beq (getN one T i) (wordJ c rm one B [one, one, one, B3I, B4I] (tW.getD i []))

end CFSG.KC.J4R0
