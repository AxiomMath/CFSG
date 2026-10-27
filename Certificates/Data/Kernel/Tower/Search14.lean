module

public import Certificates.Data.Kernel.Tower.Search

public section

namespace Certificates.KernelTower

@[expose] def cz15 (LB CZ c : Nat) : Nat := lane CZ 15 32767 (lbL LB c)

@[expose] noncomputable def labC16 (n k : Nat) (mul : Nat → Nat → Nat) (GS GI LB RP nl c : Nat) :
    Bool :=
  Nat.blt (lbL LB c) nl && Nat.blt (lbW LB c) n &&
    Nat.beq (mul (lbW LB c) (l16 RP (lbL LB c))) (mul c (lbW LB c)) &&
    allB k fun i => Nat.beq (lbL LB (mul (mul (l16 GS i) c) (l16 GI i))) (lbL LB c)

@[expose] noncomputable def labOK16 (n k : Nat) (mul : Nat → Nat → Nat) (GS GI LB RP nl : Nat) :
    Bool :=
  allB k (fun i => Nat.blt (l16 GI i) n && Nat.beq (mul (l16 GS i) (l16 GI i)) 0) &&
    allB nl (fun l => Nat.blt (l16 RP l) n && Nat.beq (lbL LB (l16 RP l)) l) &&
    allB n (labC16 n k mul GS GI LB RP nl)

@[expose] noncomputable def histB (n LB : Nat) : Nat :=
  Nat.rec 0 (fun c acc => Nat.add acc (Nat.shiftLeft 1 (Nat.mul 15 (lbL LB c)))) n

@[expose] noncomputable def czOK16 (n LB CZ : Nat) : Bool := Nat.beq (histB n LB) CZ

@[expose] noncomputable def hOK16 (n : Nat) (mul : Nat → Nat → Nat) (t HL : Nat) : Bool :=
  Nat.blt t n && allB 256 (fun j => Nat.blt (l16 HL j) n && Nat.beq (mul (l16 HL j) t) (mul t (l16 HL j))) &&
    allB 255 (fun j => Nat.blt (l16 HL j) (l16 HL (Nat.succ j))) &&
    Nat.beq (cntB n fun c => Nat.beq (mul c t) (mul t c)) 256

@[expose] def ocOf (OT LB CZ u : Nat) : Nat := Nat.add (oe OT u) (Nat.mul 4 (cz15 LB CZ u))

@[expose] def ivOf (mul : Nat → Nat → Nat) (OT LB CZ s u : Nat) : Nat :=
  Nat.add (ocOf OT LB CZ u) (Nat.shiftLeft (ocOf OT LB CZ (mul u s)) 17)

@[expose] def pvOf16 (mul : Nat → Nat → Nat) (OT LB CZ s x y : Nat) : Nat :=
  Nat.add (ocOf OT LB CZ (mul x y)) (Nat.add (Nat.shiftLeft (ocOf OT LB CZ (mul (mul x s) y)) 17)
    (Nat.add (Nat.shiftLeft (ocOf OT LB CZ (mul (mul x x) y)) 34)
      (Nat.shiftLeft (ocOf OT LB CZ (mul (mul x y) y)) 51)))

@[expose] def kyL (KY i : Nat) : Nat := lane KY 64 18446744073709551615 i

@[expose] def pvL (PV i : Nat) : Nat := lane PV 128 340282366920938463463374607431768211455 i

@[expose] def kyOK (mul : Nat → Nat → Nat) (OT LB CZ GS KY PV : Nat) : Bool :=
  Nat.beq (kyL KY 0) (ivOf mul OT LB CZ (l16 GS 0) (l16 GS 1)) &&
    Nat.beq (kyL KY 1) (ivOf mul OT LB CZ (l16 GS 0) (l16 GS 2)) &&
    Nat.beq (kyL KY 2) (ivOf mul OT LB CZ (l16 GS 0) (l16 GS 3)) &&
    Nat.beq (pvL PV 0) (pvOf16 mul OT LB CZ (l16 GS 0) (l16 GS 1) (l16 GS 2)) &&
    Nat.beq (pvL PV 1) (pvOf16 mul OT LB CZ (l16 GS 0) (l16 GS 1) (l16 GS 3)) &&
    Nat.beq (pvL PV 2) (pvOf16 mul OT LB CZ (l16 GS 0) (l16 GS 2) (l16 GS 3))

@[expose] noncomputable def cmOK16 (n : Nat) (mul : Nat → Nat → Nat) (t OT LB CZ K CL RK c : Nat) :
    Bool :=
  allB n fun u => !Nat.beq (ivOf mul OT LB CZ t u) K ||
    Nat.blt (rkL RK u) c && Nat.beq (l16 CL (rkL RK u)) u

@[expose] def e14W1 (n : Nat) (mul : Nat → Nat → Nat) (HL R1 n1 u v : Nat) : Bool :=
  Nat.blt (Nat.land v 511) n1 && Nat.blt (Nat.shiftRight v 9) 256 &&
    Nat.blt (l16 R1 (Nat.land v 511)) n &&
    Nat.beq (mul (l16 HL (Nat.shiftRight v 9)) u)
      (mul (l16 R1 (Nat.land v 511)) (l16 HL (Nat.shiftRight v 9)))

@[expose] noncomputable def e14Lvl1 (n : Nat) (mul : Nat → Nat → Nat) (HL CL c R1 W1 n1 : Nat) :
    Bool :=
  allB c fun k => e14W1 n mul HL R1 n1 (l16 CL k) (lane W1 32 4294967295 k)

@[expose] def e14P1 (R2 r2 : Nat) : Nat := Nat.land (lane R2 32 4294967295 r2) 1023

@[expose] def e14P2 (R2 r2 : Nat) : Nat := Nat.shiftRight (lane R2 32 4294967295 r2) 10

@[expose] def e14W2 (n : Nat) (mul : Nat → Nat → Nat) (HL R1 R2 n2 r1 u v : Nat) : Bool :=
  Nat.blt (Nat.land v 4095) n2 && Nat.blt (Nat.shiftRight v 12) 256 &&
    Nat.beq (e14P1 R2 (Nat.land v 4095)) r1 && Nat.blt (e14P2 R2 (Nat.land v 4095)) n &&
    Nat.beq (mul (l16 HL (Nat.shiftRight v 12)) (l16 R1 r1))
      (mul (l16 R1 r1) (l16 HL (Nat.shiftRight v 12))) &&
    Nat.beq (mul (l16 HL (Nat.shiftRight v 12)) u)
      (mul (e14P2 R2 (Nat.land v 4095)) (l16 HL (Nat.shiftRight v 12)))

@[expose] noncomputable def e14Lvl2 (n : Nat) (mul : Nat → Nat → Nat)
    (OT LB CZ t HL CL c R1 R2 P n2 W r1 : Nat) : Bool :=
  allB c fun k => !Nat.beq (pvOf16 mul OT LB CZ t (l16 R1 r1) (l16 CL k)) P ||
    e14W2 n mul HL R1 R2 n2 r1 (l16 CL k) (lane W 32 4294967295 k)

@[expose] def e14Im (t u1 u2 v : Nat) : Nat :=
  Nat.add t (Nat.add (Nat.shiftLeft u1 16) (Nat.add (Nat.shiftLeft u2 32) (Nat.shiftLeft v 48)))

@[expose] noncomputable def e14Sp (mul : Nat → Nat → Nat) (GS PT IM f o : Nat) : Bool :=
  Nat.blt (ptDep PT (Nat.land o 16383)) f &&
    Nat.blt (ptDep PT (mul (l16 GS (Nat.shiftRight o 14)) (Nat.land o 16383))) f &&
    !Nat.beq (fpK mul PT IM f (mul (l16 GS (Nat.shiftRight o 14)) (Nat.land o 16383)))
      (mul (l16 IM (Nat.shiftRight o 14)) (fpK mul PT IM f (Nat.land o 16383)))

@[expose] noncomputable def e14V (mul : Nat → Nat → Nat) (OT LB CZ t GS PT f K P13 P23 SP u1 u2 v : Nat) :
    Bool :=
  !Nat.beq (ivOf mul OT LB CZ t v) K || !Nat.beq (pvOf16 mul OT LB CZ t u1 v) P13 ||
    !Nat.beq (pvOf16 mul OT LB CZ t u2 v) P23 || e14Sp mul GS PT (e14Im t u1 u2 v) f (l16 SP v)

@[expose] noncomputable def e14Lvl3 (n : Nat) (mul : Nat → Nat → Nat) (OT LB CZ t GS PT f R1 R2 K P13 P23 SP r2 :
    Nat) : Bool :=
  allB n (e14V mul OT LB CZ t GS PT f K P13 P23 SP (l16 R1 (e14P1 R2 r2)) (e14P2 R2 r2))

end Certificates.KernelTower
