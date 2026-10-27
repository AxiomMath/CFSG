module

public import Certificates.Data.Kernel.Tower.Tree
public import Certificates.Data.Kernel.Tower.L1

public section

namespace Certificates.KernelTower

@[expose] noncomputable def allFrom (a k : Nat) (p : Nat → Bool) : Bool := allB k fun i => p (Nat.add a i)

@[expose] noncomputable def sqK (mul : Nat → Nat → Nat) (x k : Nat) : Nat :=
  Nat.rec x (fun _ y => mul y y) k

@[expose] noncomputable def ordC (mul : Nat → Nat → Nat) (c e : Nat) : Bool :=
  Nat.beq (sqK mul c e) 0 &&
    (Nat.beq e 0 && Nat.beq c 0 || Nat.blt 0 e && !Nat.beq (sqK mul c (Nat.sub e 1)) 0)

@[expose] def oe (OT c : Nat) : Nat := lane OT 2 3 c

@[expose] noncomputable def ordOK (n : Nat) (mul : Nat → Nat → Nat) (OT : Nat) : Bool :=
  allB n fun c => ordC mul c (oe OT c)

@[expose] def lbL (LB c : Nat) : Nat := Nat.land (lane LB 24 16777215 c) 255

@[expose] def lbW (LB c : Nat) : Nat := Nat.shiftRight (lane LB 24 16777215 c) 8

@[expose] def rpL (RP l : Nat) : Nat := lane RP 13 8191 l

@[expose] def czOf (LB CZ c : Nat) : Nat := lane CZ 14 16383 (lbL LB c)

@[expose] noncomputable def labC (n : Nat) (mul : Nat → Nat → Nat) (GS GI LB RP nl c : Nat) : Bool :=
  Nat.blt (lbL LB c) nl && Nat.blt (lbW LB c) n &&
    Nat.beq (mul (lbW LB c) (rpL RP (lbL LB c))) (mul c (lbW LB c)) &&
    allB 4 fun i => Nat.beq (lbL LB (mul (mul (l16 GS i) c) (l16 GI i))) (lbL LB c)

@[expose] noncomputable def labOK (n : Nat) (mul : Nat → Nat → Nat) (GS GI LB RP nl : Nat) : Bool :=
  allB 4 (fun i => Nat.blt (l16 GI i) n && Nat.beq (mul (l16 GS i) (l16 GI i)) 0) &&
    allB nl (fun l => Nat.blt (rpL RP l) n && Nat.beq (lbL LB (rpL RP l)) l) &&
    allB n (labC n mul GS GI LB RP nl)

@[expose] noncomputable def czOK (n : Nat) (LB CZ a k : Nat) : Bool :=
  allFrom a k fun l => Nat.beq (lane CZ 14 16383 l) (cntB n fun c => Nat.beq (lbL LB c) l)

@[expose] def hL (HL j : Nat) : Nat := lane HL 13 8191 j

@[expose] def hC (mul : Nat → Nat → Nat) (HL j u : Nat) : Bool :=
  Nat.beq (mul (hL HL j) u) (mul u (hL HL j))

@[expose] noncomputable def hOK (n : Nat) (mul : Nat → Nat → Nat) (t HL : Nat) : Bool :=
  allB 128 (fun j => Nat.blt (hL HL j) n && hC mul HL j t) &&
    allB 127 (fun j => Nat.blt (hL HL j) (hL HL (Nat.succ j))) &&
    Nat.beq (cntB n fun c => Nat.beq (mul c t) (mul t c)) 128

@[expose] noncomputable def cntH (mul : Nat → Nat → Nat) (HL u : Nat) : Nat :=
  cntB 128 fun j => hC mul HL j u

@[expose] noncomputable def candB (mul : Nat → Nat → Nat) (t OT LB CZ HL w cw u : Nat) : Bool :=
  Nat.beq (oe OT u) (oe OT w) && Nat.beq (oe OT (mul u t)) (oe OT (mul w t)) &&
    Nat.beq (czOf LB CZ u) (czOf LB CZ w) && Nat.beq (cntH mul HL u) cw

@[expose] def clL (CL k : Nat) : Nat := lane CL 13 8191 k

@[expose] def rkL (RK u : Nat) : Nat := lane RK 10 1023 u

@[expose] noncomputable def cmOK (n : Nat) (mul : Nat → Nat → Nat) (t OT LB CZ HL w cw CL RK c : Nat) :
    Bool :=
  Nat.beq (cntH mul HL w) cw &&
    allB n fun u => !candB mul t OT LB CZ HL w cw u ||
      Nat.blt (rkL RK u) c && Nat.beq (clL CL (rkL RK u)) u

@[expose] def pvOf (mul : Nat → Nat → Nat) (t OT x y : Nat) : Nat :=
  Nat.add (oe OT (mul x y)) (Nat.add (Nat.mul 4 (oe OT (mul (mul x t) (mul y t))))
    (Nat.add (Nat.mul 16 (oe OT (mul (mul x x) y))) (Nat.mul 64 (oe OT (mul (mul x y) y)))))

@[expose] def ipE (mul : Nat → Nat → Nat) (t OT P x y : Nat) : Bool :=
  Nat.beq (oe OT (mul x y)) (lane P 2 3 0) &&
    Nat.beq (oe OT (mul (mul x t) (mul y t))) (lane P 2 3 1) &&
    Nat.beq (oe OT (mul (mul x x) y)) (lane P 2 3 2) &&
    Nat.beq (oe OT (mul (mul x y) y)) (lane P 2 3 3)

@[expose] def pvOK (mul : Nat → Nat → Nat) (t OT GS PV : Nat) : Bool :=
  Nat.beq (lane PV 8 255 0) (pvOf mul t OT (l16 GS 1) (l16 GS 2)) &&
    Nat.beq (lane PV 8 255 1) (pvOf mul t OT (l16 GS 1) (l16 GS 3)) &&
    Nat.beq (lane PV 8 255 2) (pvOf mul t OT (l16 GS 2) (l16 GS 3))

@[expose] def w1C (mul : Nat → Nat → Nat) (HL R1 n1 u v : Nat) : Bool :=
  Nat.blt (Nat.land v 511) n1 && Nat.blt (Nat.shiftRight v 9) 128 &&
    Nat.beq (mul (hL HL (Nat.shiftRight v 9)) u)
      (mul (lane R1 13 8191 (Nat.land v 511)) (hL HL (Nat.shiftRight v 9)))

@[expose] noncomputable def lvl1B (mul : Nat → Nat → Nat) (HL CL c R1 W1 n1 : Nat) : Bool :=
  allB c fun k => w1C mul HL R1 n1 (clL CL k) (lane W1 16 65535 k)

@[expose] def r2u1 (R1 R2 r2 : Nat) : Nat := lane R1 13 8191 (Nat.land (lane R2 24 16777215 r2) 1023)

@[expose] def r2u2 (R2 r2 : Nat) : Nat := Nat.shiftRight (lane R2 24 16777215 r2) 10

@[expose] def w2C (mul : Nat → Nat → Nat) (HL R1 R2 n2 r1 u v : Nat) : Bool :=
  Nat.blt (Nat.land v 4095) n2 && Nat.blt (Nat.shiftRight v 12) 128 &&
    Nat.beq (Nat.land (lane R2 24 16777215 (Nat.land v 4095)) 1023) r1 &&
    hC mul HL (Nat.shiftRight v 12) (lane R1 13 8191 r1) &&
    Nat.beq (mul (hL HL (Nat.shiftRight v 12)) u)
      (mul (r2u2 R2 (Nat.land v 4095)) (hL HL (Nat.shiftRight v 12)))

@[expose] noncomputable def lvl2At (mul : Nat → Nat → Nat) (t OT HL CL c R1 R2 PV n2 W r1 : Nat) :
    Bool :=
  allB c fun k => !ipE mul t OT (lane PV 8 255 0) (lane R1 13 8191 r1) (clL CL k) ||
    w2C mul HL R1 R2 n2 r1 (clL CL k) (lane W 20 1048575 k)

@[expose] def r3L (R3 r3 : Nat) : Nat := lane R3 48 281474976710655 r3

@[expose] def w3C (mul : Nat → Nat → Nat) (HL R1 R2 R3 n3 r2 u v : Nat) : Bool :=
  Nat.blt (Nat.land v 131071) n3 && Nat.blt (Nat.shiftRight v 17) 128 &&
    Nat.beq (Nat.land (r3L R3 (Nat.land v 131071)) 4095) r2 &&
    hC mul HL (Nat.shiftRight v 17) (r2u1 R1 R2 r2) && hC mul HL (Nat.shiftRight v 17) (r2u2 R2 r2) &&
    Nat.beq (mul (hL HL (Nat.shiftRight v 17)) u)
      (mul (Nat.land (Nat.shiftRight (r3L R3 (Nat.land v 131071)) 12) 8191)
        (hL HL (Nat.shiftRight v 17)))

@[expose] noncomputable def lvl3At (mul : Nat → Nat → Nat) (t OT HL CL c R1 R2 R3 PV n3 W r2 : Nat) :
    Bool :=
  allB c fun k => !ipE mul t OT (lane PV 8 255 1) (r2u1 R1 R2 r2) (clL CL k) ||
    !ipE mul t OT (lane PV 8 255 2) (r2u2 R2 r2) (clL CL k) ||
    w3C mul HL R1 R2 R3 n3 r2 (clL CL k) (lane W 24 16777215 k)

@[expose] noncomputable def fpK (mul : Nat → Nat → Nat) (PT IM f c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih c => cond (Nat.beq c 0) 0 (mul (l16 IM (ptGi PT c)) (ih (ptPar PT c)))) f c

@[expose] noncomputable def outC (n : Nat) (mul : Nat → Nat → Nat) (GS PT AI na IM o : Nat) : Bool :=
  cond (Nat.beq (Nat.land o 1) 0)
    (Nat.blt (Nat.shiftRight o 1) na &&
      Nat.beq (Nat.land (Nat.shiftRight AI (Nat.mul 64 (Nat.shiftRight o 1))) 18446744073709551615) IM)
    (Nat.blt (Nat.land (Nat.shiftRight o 1) 8191) n && Nat.blt (Nat.shiftRight o 14) 4 &&
      Nat.blt (ptDep PT (Nat.land (Nat.shiftRight o 1) 8191)) 16 &&
      Nat.blt (ptDep PT (mul (l16 GS (Nat.shiftRight o 14)) (Nat.land (Nat.shiftRight o 1) 8191))) 16 &&
      !Nat.beq (fpK mul PT IM 16 (mul (l16 GS (Nat.shiftRight o 14)) (Nat.land (Nat.shiftRight o 1) 8191)))
        (mul (l16 IM (Nat.shiftRight o 14)) (fpK mul PT IM 16 (Nat.land (Nat.shiftRight o 1) 8191))))

@[expose] def r3IM (t R1 R2 R3 r3 : Nat) : Nat :=
  Nat.add t (Nat.add (Nat.shiftLeft (r2u1 R1 R2 (Nat.land (r3L R3 r3) 4095)) 16)
    (Nat.add (Nat.shiftLeft (r2u2 R2 (Nat.land (r3L R3 r3) 4095)) 32)
      (Nat.shiftLeft (Nat.land (Nat.shiftRight (r3L R3 r3) 12) 8191) 48)))

@[expose] noncomputable def r3OK (n : Nat) (mul : Nat → Nat → Nat) (t GS PT AI na R1 R2 R3 n2 a k : Nat) :
    Bool :=
  allFrom a k fun r3 => Nat.blt (Nat.land (r3L R3 r3) 4095) n2 &&
    outC n mul GS PT AI na (r3IM t R1 R2 R3 r3) (Nat.shiftRight (r3L R3 r3) 25)

end Certificates.KernelTower
