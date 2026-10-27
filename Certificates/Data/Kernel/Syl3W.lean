module

public import Certificates.Data.Kernel.BalanceSC.Sylow

public section

namespace CFSG.KC.Syl3W

open CFSG.KC.Enum (strictB)
open CFSG.KC.LQT.P (allN anyN)
open CFSG.KC.BalanceSC (getL notB)

@[expose] noncomputable def slot (P i : Nat) : Nat :=
  fld(P, Nat.mul (nat_lit 288) i,
    nat_lit 497323236409786642155382248146820840100456150797347717440463976893159497012533375533055)

@[expose] noncomputable def ln (A e : Nat) : Nat := fld(A, Nat.mul (nat_lit 8) e, nat_lit 255)

@[expose] noncomputable def ln7 (P e : Nat) : Nat := fld(P, Nat.mul (nat_lit 7) e, nat_lit 127)

@[expose] noncomputable def rowS (A r : Nat) : Nat :=
  Nat.add (ln A (Nat.mul 6 r)) (Nat.add (ln A (Nat.add (Nat.mul 6 r) 1))
    (Nat.add (ln A (Nat.add (Nat.mul 6 r) 2)) (Nat.add (ln A (Nat.add (Nat.mul 6 r) 3))
      (Nat.add (ln A (Nat.add (Nat.mul 6 r) 4)) (ln A (Nat.add (Nat.mul 6 r) 5))))))

@[expose] noncomputable def colS (B c : Nat) : Nat :=
  Nat.add (ln B c) (Nat.add (ln B (Nat.add 6 c)) (Nat.add (ln B (Nat.add 12 c))
    (Nat.add (ln B (Nat.add 18 c)) (Nat.add (ln B (Nat.add 24 c)) (ln B (Nat.add 30 c))))))

@[expose] noncomputable def dotS (A B r c : Nat) : Nat :=
  Nat.add (Nat.mul (ln A (Nat.mul 6 r)) (ln B c))
    (Nat.add (Nat.mul (ln A (Nat.add (Nat.mul 6 r) 1)) (ln B (Nat.add 6 c)))
    (Nat.add (Nat.mul (ln A (Nat.add (Nat.mul 6 r) 2)) (ln B (Nat.add 12 c)))
    (Nat.add (Nat.mul (ln A (Nat.add (Nat.mul 6 r) 3)) (ln B (Nat.add 18 c)))
    (Nat.add (Nat.mul (ln A (Nat.add (Nat.mul 6 r) 4)) (ln B (Nat.add 24 c)))
      (Nat.mul (ln A (Nat.add (Nat.mul 6 r) 5)) (ln B (Nat.add 30 c)))))))

@[expose] noncomputable def prodOK (A B C : Nat) : Bool :=
  allN 6 fun r => allN 6 fun c =>
    Nat.beq (Nat.add (dotS A B r c) 60100)
      (Nat.add (ln C (Nat.add (Nat.mul 6 r) c)) (Nat.mul 100 (Nat.add (rowS A r) (colS B c))))

@[expose] noncomputable def tabK (MP GP TB : Nat) : Bool :=
  allN 81 fun i => strictB (slot MP i) fun A => allN 4 fun k =>
    strictB (ln7 TB (Nat.add (Nat.mul 4 i) k)) fun t =>
      bAnd(Nat.blt t 81, prodOK A (slot GP k) (slot MP t))

@[expose] noncomputable def invK (GP ONE : Nat) : Bool :=
  bAnd(prodOK (slot GP 0) (slot GP 1) ONE, bAnd(prodOK (slot GP 1) (slot GP 0) ONE,
    bAnd(prodOK (slot GP 2) (slot GP 3) ONE, prodOK (slot GP 3) (slot GP 2) ONE)))

@[expose] noncomputable def chainK (RF : List Nat) (ONE : Nat) : List Nat → List Nat → Bool :=
  fun w S => List.rec (motive := fun _ => List Nat → Bool)
    (fun S => Nat.beq (getL 0 S 0) ONE)
    (fun s _ ih S => bAnd(prodOK (getL 0 RF s) (getL 0 S 1) (getL 0 S 0), ih S.tail)) w S

@[expose] noncomputable def genK (RF : List Nat) (ONE GP : Nat) (SW SG : List (List Nat)) : Bool :=
  allN 4 fun k => bAnd(Nat.beq (getL 0 (getL [] SG k) 0) (slot GP k),
    chainK RF ONE (getL [] SW k) (getL [] SG k))

@[expose] noncomputable def eltK (MP GP ONE : Nat) (W SX : List (List Nat)) : Bool :=
  allN 81 fun i => bAnd(Nat.beq (getL 0 ((getL [] SX i).map (slot MP)) 0) (slot MP i),
    chainK ((List.range 4).map (slot GP)) ONE (getL [] W i) ((getL [] SX i).map (slot MP)))

@[expose] noncomputable def mtK (MT TB : Nat) (WP WL : List Nat) : Bool :=
  allN 81 fun i => allN 81 fun j =>
    bIf(Nat.beq j 0, Nat.beq (ln7 MT (Nat.mul 81 i)) i,
      bAnd(Nat.blt (getL 0 WP j) j, bAnd(Nat.blt (getL 0 WL j) 4,
        Nat.beq (ln7 MT (Nat.add (Nat.mul 81 i) j))
          (ln7 TB (Nat.add (Nat.mul 4 (ln7 MT (Nat.add (Nat.mul 81 i) (getL 0 WP j))))
            (getL 0 WL j))))))

@[expose] noncomputable def cntK (x m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun n acc => Nat.add acc (Nat.land (Nat.shiftRight x n) 1)) m

@[expose] noncomputable def mulK (MT i j : Nat) : Nat := ln7 MT (Nat.add (Nat.mul 81 i) j)

@[expose] noncomputable def ord3K (MT i : Nat) : Bool :=
  bAnd(notB (Nat.beq i 0), Nat.beq (mulK MT (mulK MT i i) i) 0)

@[expose] noncomputable def commK (MT i j : Nat) : Bool := Nat.beq (mulK MT i j) (mulK MT j i)

@[expose] noncomputable def indepK (MT i j : Nat) : Bool :=
  bAnd(notB (Nat.beq j 0), bAnd(notB (Nat.beq j i), notB (Nat.beq j (mulK MT i i))))

@[expose] noncomputable def powK (MT i a : Nat) : Nat :=
  nIf(Nat.beq a 0, 0, nIf(Nat.beq a 1, i, mulK MT i i))

@[expose] noncomputable def outK (MT i j k : Nat) : Bool :=
  allN 3 fun a => allN 3 fun b => notB (Nat.beq k (mulK MT (powK MT i a) (powK MT j b)))

@[expose] noncomputable def p12K (MT : Nat) (FM : List Nat) : Bool :=
  allN 81 fun i => bIf(ord3K MT i, strictB (getL 0 FM i) fun Fi => allN 81 fun j =>
    bIf(bAnd(ord3K MT j, bAnd(commK MT i j, indepK MT i j)),
      strictB (Nat.land Fi (getL 0 FM j)) fun F =>
        bAnd(Nat.ble (cntK F 729) 9, allN 81 fun k =>
          bIf(bAnd(ord3K MT k, bAnd(commK MT i k, bAnd(commK MT j k, outK MT i j k))),
            Nat.ble (cntK (Nat.land F (getL 0 FM k)) 729) 3, true)),
      true), true)

@[expose] noncomputable def dg (n t : Nat) : Nat := Nat.mod (Nat.div n (Nat.pow 3 t)) 3

@[expose] noncomputable def fixC (A n c : Nat) : Bool :=
  Nat.beq (Nat.mod (Nat.add (Nat.add
    (Nat.add (Nat.mul (dg n 0) (ln A c)) (Nat.add (Nat.mul (dg n 1) (ln A (Nat.add 6 c)))
      (Nat.add (Nat.mul (dg n 2) (ln A (Nat.add 12 c))) (Nat.add (Nat.mul (dg n 3) (ln A (Nat.add 18 c)))
        (Nat.add (Nat.mul (dg n 4) (ln A (Nat.add 24 c))) (Nat.mul (dg n 5) (ln A (Nat.add 30 c))))))))
    (Nat.mul 2 (Nat.add (dg n 0) (Nat.add (dg n 1) (Nat.add (dg n 2) (Nat.add (dg n 3)
      (Nat.add (dg n 4) (dg n 5))))))))
    (Nat.mul 2 (dg n c))) 3) 0

@[expose] noncomputable def fixP (A n : Nat) : Bool := allN 6 fun c => fixC A n c

@[expose] noncomputable def fmK (MP : Nat) (FM : List Nat) : Bool :=
  allN 81 fun i => strictB (slot MP i) fun A => strictB (getL 0 FM i) fun F =>
    allN 27 fun h => allN 27 fun l => strictB (Nat.add (Nat.mul 27 h) l) fun n =>
      Bool.rec (notB (fixP A n)) (fixP A n) (Nat.beq (Nat.land (Nat.shiftRight F n) 1) 1)

@[expose] noncomputable def codesW (P len : Nat) (L : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun n => Nat.beq n len)
    (fun c _ ih n => bAnd(Nat.beq c (ln P n), ih (Nat.succ n))) L

@[expose] noncomputable def codesK (L : List Nat) (P len : Nat) : Bool := codesW P len L 0

@[expose] noncomputable def distK (MP : Nat) : Bool :=
  allN 81 fun i => strictB (slot MP i) fun A => allN 81 fun j =>
    bIf(Nat.beq i j, true, strictB (slot MP j) fun B =>
      anyN 36 fun e => notB (Nat.beq (ln A e) (ln B e)))

end CFSG.KC.Syl3W

end
