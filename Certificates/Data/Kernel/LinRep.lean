module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.LinRep

open CFSG.KC.Enum

@[expose] noncomputable def nB (b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false b

@[expose] noncomputable def c6 (x i : Nat) : Nat := Nat.land (Nat.shiftRight x (Nat.mul 6 i)) 63

@[expose] noncomputable def bm (v i y : Nat) : Nat := Nat.mul (Nat.land (Nat.shiftRight v i) 1) y

@[expose] noncomputable def appW (a v : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (bm v 0 (c6 a 0)) (bm v 1 (c6 a 1)))
    (bm v 2 (c6 a 2))) (bm v 3 (c6 a 3))) (bm v 4 (c6 a 4))) (bm v 5 (c6 a 5))

@[expose] noncomputable def w6 (x0 x1 x2 x3 x4 x5 : Nat) : Nat :=
  Nat.add x0 (Nat.mul 64 (Nat.add x1 (Nat.mul 64 (Nat.add x2 (Nat.mul 64 (Nat.add x3
    (Nat.mul 64 (Nat.add x4 (Nat.mul 64 x5)))))))))

@[expose] noncomputable def mulW (a b : Nat) : Nat :=
  w6 (appW a (c6 b 0)) (appW a (c6 b 1)) (appW a (c6 b 2)) (appW a (c6 b 3)) (appW a (c6 b 4))
    (appW a (c6 b 5))

@[expose] noncomputable def mulT (G b : Nat) : Nat :=
  w6 (c6 G (c6 b 0)) (c6 G (c6 b 1)) (c6 G (c6 b 2)) (c6 G (c6 b 3)) (c6 G (c6 b 4)) (c6 G (c6 b 5))

@[expose] noncomputable def idW : Nat := 34630287489

@[expose] noncomputable def tabW (a : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun v acc => Nat.add acc (Nat.shiftLeft (appW a v) (Nat.mul 6 v))) 64

@[expose] noncomputable def tab7 (a : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun v acc => Nat.add acc (Nat.shiftLeft (appW a v) (Nat.mul 7 v))) 64

@[expose] noncomputable def nthN (L : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) i) L i

@[expose] noncomputable def slot (E : Nat → Nat) (p : Nat) : Nat :=
  Nat.land (Nat.shiftRight (E (Nat.shiftRight p 10)) (Nat.shiftLeft (Nat.land p 1023) 6))
    18446744073709551615

@[expose] noncomputable def key (s : Nat) : Nat := Nat.land s 68719476735

@[expose] noncomputable def spar (s : Nat) : Nat := Nat.land (Nat.shiftRight s 36) 65535

@[expose] noncomputable def slab (s : Nat) : Nat := Nat.land (Nat.shiftRight s 52) 15

@[expose] noncomputable def row (R l : Nat) : Nat :=
  Nat.land (Nat.shiftRight R (Nat.shiftLeft l 8))
    115792089237316195423570985008687907853269984665640564039457584007913129639935

@[expose] noncomputable def pos16 (r j : Nat) : Nat := Nat.land (Nat.shiftRight r (Nat.shiftLeft j 4)) 65535

@[expose] noncomputable def lexB (a b c d : Nat) : Bool := bIf(Nat.blt a c, true, bAnd(Nat.beq a c, Nat.blt b d))

@[expose] noncomputable def closeJ (E : Nat → Nat) (cnt w h r : Nat) (GS : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun G _ ih j => strictB (pos16 r j) fun p => strictB (slot E p) fun s =>
      bAnd(Nat.blt p cnt, bAnd(Nat.beq (mulT G w) (key s),
        bAnd(bIf(Nat.beq p 0, true, nB (lexB h j (spar s) (slab s))), strictB (Nat.succ j) ih))))
    GS 0

@[expose] noncomputable def rowK (E : Nat → Nat) (GS : List Nat) (k cnt r h : Nat) : Bool :=
  strictB (slot E h) fun s => strictB (key s) fun w =>
    bAnd(bIf(Nat.beq h 0, true, bAnd(Nat.blt (spar s) h, bAnd(Nat.blt (slab s) k,
        Nat.beq w (mulT (nthN GS (slab s)) (key (slot E (spar s))))))),
      bAnd(bIf(Nat.beq h 0, true, bIf(Nat.blt (Nat.succ h) cnt,
          strictB (slot E (Nat.succ h)) fun s' => lexB (spar s) (slab s) (spar s') (slab s'), true)),
        closeJ E cnt w h r GS))

@[expose] noncomputable def segK (E : Nat → Nat) (GS : List Nat) (k cnt R lo len : Nat) : Bool :=
  allN len fun l => rowK E GS k cnt (row R l) (Nat.add lo l)

@[expose] noncomputable def tabsK (GW GT : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun T => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) T)
    (fun a _ ih T => List.rec (motive := fun _ => Bool) false
      (fun t T' _ => bAnd(Nat.beq (tabW a) t, ih T')) T) GW GT

@[expose] noncomputable def headK (E : Nat → Nat) (GW GT : List Nat) (cnt : Nat) : Bool :=
  bAnd(Nat.blt 0 cnt, strictB (slot E 0) fun s => bAnd(Nat.beq (key s) idW,
    bAnd(Nat.beq (spar s) 0, bAnd(Nat.beq (slab s) 0, tabsK GW GT))))

@[expose] noncomputable def incK (E : Nat → Nat) (cnt : Nat) (L : List Nat) : Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ c => Nat.beq c cnt)
    (fun i _ ih prev c => bAnd(Nat.blt i cnt, strictB (key (slot E i)) fun x =>
      bAnd(Nat.blt prev x, strictB (Nat.succ c) (ih x)))) L

@[expose] noncomputable def ordK (E : Nat → Nat) (cnt : Nat) (ORD : List Nat) : Bool :=
  incK E cnt ORD 0 0

@[expose] noncomputable def invW (Y0 Y1 g iw : Nat) : Bool :=
  bIf(Nat.blt iw 6, nB (Nat.beq (appW g (c6 g iw)) (Nat.shiftLeft 1 iw)),
    bIf(Nat.beq iw 6, Nat.beq g idW,
      bAnd(Nat.beq (mulW g g) idW,
        strictB (Nat.land (Nat.sub iw 8) 7) fun c =>
          strictB (nIf(Nat.blt (Nat.sub iw 8) 8, Y0, Y1)) fun Y =>
            strictB (mulW Y (mulW g (mulW Y Y))) fun Z =>
              nB (Nat.beq (appW g (c6 Z c)) (appW Z (c6 g c))))))

@[expose] noncomputable def invK (E : Nat → Nat) (Y0 Y1 lo len : Nat) : Bool :=
  allN len fun l => strictB (slot E (Nat.add lo l)) fun s =>
    invW Y0 Y1 (key s) (Nat.shiftRight s 56)

end CFSG.KC.LinRep

end
