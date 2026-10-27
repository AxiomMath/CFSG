module

public import Certificates.Data.Kernel.Sp6A2K
public import Certificates.Data.Kernel.Misc.PermClos

public section

namespace CFSG.KD.Sp6RefS

open CFSG.KD.Sp62 CFSG.KC.Loop
open CFSG.KD.Sp6A2 (strictB)

@[expose] noncomputable def commB (a b : Nat) : Bool := Nat.beq (MULF a b) (MULF b a)

@[expose] noncomputable def aStep (Z A : Nat → Nat) (i : Nat) : Bool :=
  cond (Nat.beq (Nat.mod (Nat.succ i) 3) 0)
    (cond (Nat.beq (Nat.mod (Nat.div (Nat.succ i) 3) 3) 0)
      (Nat.beq (A (Nat.succ i)) (MULF (A (Nat.sub (Nat.succ i) 9)) (Z 0)))
      (Nat.beq (A (Nat.succ i)) (MULF (A (Nat.sub (Nat.succ i) 3)) (Z 1))))
    (Nat.beq (A (Nat.succ i)) (MULF (A i) (Z 2)))

@[expose] noncomputable def aK (Z A : Nat → Nat) : Bool :=
  Nat.beq (A 0) ONE && allBelow 26 1 (aStep Z A)

@[expose] noncomputable def addIdx (i m : Nat) : Nat :=
  Nat.add (Nat.add (Nat.mul 9 (Nat.mod (Nat.add (Nat.div i 9) (Nat.div m 9)) 3))
    (Nat.mul 3 (Nat.mod (Nat.add (Nat.mod (Nat.div i 3) 3) (Nat.mod (Nat.div m 3) 3)) 3)))
    (Nat.mod (Nat.add (Nat.mod i 3) (Nat.mod m 3)) 3)

@[expose] noncomputable def aAddK (A : Nat → Nat) : Bool :=
  allBelow 729 12 fun p => Nat.beq (MULF (A (Nat.div p 27)) (A (Nat.mod p 27)))
    (A (addIdx (Nat.div p 27) (Nat.mod p 27)))

@[expose] noncomputable def wK (WG WX WP WC : Nat → Nat) : Bool :=
  Nat.beq (WX 0) ONE &&
    buildG (rmulSt WG) WX (fun i => Nat.land (WP i) 255) (fun i => Nat.shiftRight (WP i) 8) 48 3 1 &&
    allBelow 144 3 fun i => Nat.blt (WC i) 48 &&
      Nat.beq (WX (WC i)) (MULF (WX (Nat.div i 3)) (WG (Nat.mod i 3)))

@[expose] noncomputable def wmK (Z A WX WM : Nat → Nat) : Bool :=
  allBelow 144 3 fun p => Nat.blt (WM p) 27 &&
    Nat.beq (MULF (WX (Nat.div p 3)) (Z (Nat.mod p 3))) (MULF (A (WM p)) (WX (Nat.div p 3)))

@[expose] noncomputable def elt (A WX : Nat → Nat) (n : Nat) : Nat :=
  MULF (A (Nat.div n 48)) (WX (Nat.mod n 48))

@[expose] noncomputable def lC (Z : Nat → Nat) (a : Nat) : Nat :=
  cond (Nat.beq (Nat.mod a 2) 0) (Z (Nat.div a 2)) (MULF (Z (Nat.div a 2)) (Z (Nat.div a 2)))

@[expose] noncomputable def distH (a b c : Nat) : Bool :=
  !(Nat.beq (Nat.div a 2) (Nat.div b 2)) && !(Nat.beq (Nat.div a 2) (Nat.div c 2)) &&
    !(Nat.beq (Nat.div b 2) (Nat.div c 2))

@[expose] noncomputable def frameAt (Z : Nat → Nat) (n a b c : Nat) : Bool :=
  Nat.beq (MULF n (Z 0)) (MULF (lC Z a) n) && Nat.beq (MULF n (Z 1)) (MULF (lC Z b) n) &&
    Nat.beq (MULF n (Z 2)) (MULF (lC Z c) n)

@[expose] noncomputable def frameK (Z A WX FR : Nat → Nat) : Bool :=
  allBelow 216 4 fun t =>
    !(distH (Nat.div t 36) (Nat.mod (Nat.div t 6) 6) (Nat.mod t 6)) ||
      (Nat.blt (FR t) 1296 &&
        frameAt Z (elt A WX (FR t)) (Nat.div t 36) (Nat.mod (Nat.div t 6) 6) (Nat.mod t 6))

@[expose] noncomputable def cmask (A : Nat → Nat) (s : Nat) : Nat :=
  sumBelow 27 1 fun x => cond (commB s (A x)) (Nat.shiftLeft 1 x) 0

@[expose] noncomputable def lineMask (x : Nat) : Nat :=
  Nat.lor (Nat.lor 1 (Nat.shiftLeft 1 x)) (Nat.shiftLeft 1 (addIdx x x))

@[expose] noncomputable def wtIdx (x : Nat) : Nat :=
  Nat.add (Nat.add (cond (Nat.beq (Nat.div x 9) 0) 0 1) (cond (Nat.beq (Nat.mod (Nat.div x 3) 3) 0) 0 1))
    (cond (Nat.beq (Nat.mod x 3) 0) 0 1)

@[expose] noncomputable def recAt (A WX RS RI RW : Nat → Nat) (s x r : Nat) : Bool :=
  Nat.blt (Nat.land r 2047) 1296 && Nat.blt (Nat.shiftRight r 11) 5 &&
    Nat.beq (MULF (elt A WX (Nat.land r 2047)) (RS (Nat.shiftRight r 11)))
      (MULF s (elt A WX (Nat.land r 2047))) &&
    Nat.beq (MULF (elt A WX (Nat.land r 2047)) (A (RI (Nat.shiftRight r 11))))
      (MULF (A x) (elt A WX (Nat.land r 2047))) &&
    Nat.beq (RW (Nat.shiftRight r 11)) (wtIdx x)

@[expose] noncomputable def lookAt (A WX RT RS RI RW : Nat → Nat) (s M q : Nat) : Bool :=
  allBelow 27 1 fun x => Nat.beq x 0 || !(Nat.testBit M x) ||
    Nat.beq (Nat.land M (Nat.xor (lineMask x) 134217727)) 0 ||
    recAt A WX RS RI RW s x (RT (Nat.add (Nat.mul 27 q) x))

@[expose] noncomputable def lookK (A WX QI RT RS RI RW : Nat → Nat) : Bool :=
  allBelow 1296 21 fun n =>
    strictB (elt A WX n) fun s =>
      !(Nat.beq (MULF s s) ONE && !(Nat.beq s ONE)) ||
        (Nat.blt (QI n) 135 && strictB (cmask A s) fun M => lookAt A WX RT RS RI RW s M (QI n))

@[expose] noncomputable def c7K (CG CX CP CS : Nat → Nat) (w : Nat) : Bool :=
  commB (CG 0) w && commB (CG 1) w &&
    allBelow 648 11 (CFSG.KC.Misc.Clos.treeAt MULF ONE CG 2 CX CP) &&
    allBelow 648 11 (CFSG.KC.Misc.Clos.sortAt 648 CX CS)

@[expose] noncomputable def conjH (HG HI : Nat → Nat) (x l : Nat) : Nat := MULF (MULF (HG l) x) (HI l)

@[expose] noncomputable def orbK (HG HI OX OP OS : Nat → Nat) (w : Nat) : Bool :=
  Nat.beq (MULF (HG 0) (HI 0)) ONE && Nat.beq (MULF (HG 1) (HI 1)) ONE &&
    allBelow 2240 35 (CFSG.KC.Misc.Clos.treeAt (conjH HG HI) w (fun l => l) 2 OX OP) &&
    allBelow 2240 35 (CFSG.KC.Misc.Clos.sortAt 2240 OX OS)

@[expose] noncomputable def rTabK (RG RX RP RC : Nat → Nat) (nG nR s l : Nat) : Bool :=
  allBelow nR 1 (CFSG.KC.Misc.Clos.treeAt MULF ONE RG nG RX RP) &&
    allBelow nR 1 (CFSG.KC.Misc.Clos.closedAt MULF RG nG nR RX RC) &&
    allBelow nR 1 (CFSG.KC.Misc.Clos.sortAt nR RX fun i => RC (Nat.add (Nat.mul nR nG) i)) &&
    allBelow nR 1 fun i => commB (RX i) s && commB (RX i) l

@[expose] noncomputable def repRec (TX RG RX : Nat → Nat) (n nG nR s x r : Nat) : Bool :=
  allBelow nG 1 (fun g => Nat.blt (Nat.land (Nat.shiftRight r (Nat.mul 3 (Nat.succ g))) 7) nR &&
      Nat.beq (MULF (RX (Nat.land (Nat.shiftRight r (Nat.mul 3 (Nat.succ g))) 7)) x) (MULF x (RG g))) &&
    ((Nat.blt (Nat.land r 7) nR && Nat.beq (RX (Nat.land r 7)) x) || !(Nat.beq (P2K x 9) ONE) ||
      (Nat.blt (Nat.land (Nat.shiftRight r 12) 4095) n && Nat.blt (Nat.shiftRight r 24) n &&
        Nat.beq (MULF (TX (Nat.land (Nat.shiftRight r 12) 4095)) (TX (Nat.shiftRight r 24))) ONE &&
        commB (TX (Nat.land (Nat.shiftRight r 12) 4095)) s &&
        !(Nat.beq (P2K (MULF x (MULF (MULF (TX (Nat.land (Nat.shiftRight r 12) 4095)) x)
          (TX (Nat.shiftRight r 24)))) 9) ONE)))

@[expose] noncomputable def repK (TX RG RX RR : Nat → Nat) (n hi nG nR s : Nat) : Bool :=
  allBelow n hi fun p => strictB (TX p) fun x =>
    !(commB x s) || repRec TX RG RX n nG nR s x (RR p)

@[expose] noncomputable def abK (RX : Nat → Nat) (nR : Nat) : Bool :=
  allBelow (Nat.mul nR nR) 1 (fun p => commB (RX (Nat.div p nR)) (RX (Nat.mod p nR))) &&
    allBelow nR 1 fun i => Nat.beq (MULF (RX i) (RX i)) ONE

@[expose] noncomputable def letH (HG HI : Nat → Nat) (l : Nat) : Nat :=
  Bool.rec (HI (Nat.sub l 2)) (HG l) (Nat.blt l 2)

@[expose] noncomputable def wordH (HG HI : Nat → Nat) (n v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ONE
    (fun i acc => MULF acc (letH HG HI (Nat.land (Nat.shiftRight v (Nat.mul 2 i)) 3))) n

@[expose] noncomputable def slK (HG HI : Nat → Nat) (n v w t : Nat) : Bool :=
  strictB (wordH HG HI n v) fun g => Nat.beq (MULF g w) (MULF t g)

end CFSG.KD.Sp6RefS
