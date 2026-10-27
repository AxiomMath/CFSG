module

public import Certificates.Data.Kernel.T10Code

public section

namespace CFSG.KC.ModZCode

open CFSG.KC.T10Code

@[expose] def commc (mul : Nat → Nat → Nat) (g x : Nat) : Bool := Nat.beq (mul g x) (mul x g)

@[expose] noncomputable def powC (mul : Nat → Nat → Nat) (y e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun _ acc => mul acc y) e

@[expose] noncomputable def sqMask (mul : Nat → Nat → Nat) (K : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun g acc => Nat.lor acc (Nat.shiftLeft 1 (mul g g))) K

@[expose] noncomputable def cntB (p : Nat → Bool) (nb : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun b acc => Nat.add acc (cntN (fun i => p (Nat.add (Nat.mul 128 b) i)) 128)) nb

@[expose] noncomputable def FE (mul : Nat → Nat → Nat) (K : Nat) (inEc : Nat → Bool) (SQ N x : Nat) :
    Bool :=
  inEc x == (Nat.beq x 0 || (Nat.beq (mul x x) 0 && tb SQ x &&
    Nat.ble N (cntB (fun g => commc mul g x) (Nat.div K 128))))

@[expose] noncomputable def F1 (mul : Nat → Nat → Nat) (K N e tc r y g h : Nat) : Bool :=
  !Nat.beq (cntB (fun y => commc mul y r) (Nat.div K 128)) N ||
    (Nat.blt y K && commc mul y r && !Nat.beq (powC mul y e) 0) ||
    (Nat.blt g K && Nat.beq (mul g h) 0 && commc mul (mul (mul g r) h) tc)

@[expose] noncomputable def memN (r : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ acc => Nat.beq a r || acc) L

@[expose] noncomputable def allF1 (mul : Nat → Nat → Nat) (K N e tc : Nat)
    (W : List (Nat × Nat × Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ acc => Bool.rec (motive := fun _ => Bool) false acc
      (F1 mul K N e tc w.1 w.2.1 w.2.2.1 w.2.2.2)) W

@[expose] def lane (T x : Nat) : Nat := Nat.land (Nat.shiftRight T (Nat.mul 16 x)) 65535

@[expose] noncomputable def F2 (mul : Nat → Nat → Nat) (K : Nat) (inMc inAc : Nat → Bool)
    (Rc : List Nat) (wr wg wh : Nat → Nat) (x : Nat) : Bool :=
  !inMc x || inAc x || !Nat.beq (mul x x) 0 ||
    (memN (wr x) Rc && Nat.blt (wg x) K && Nat.beq (mul (wg x) (wh x)) 0 &&
      Nat.beq (mul (mul (wg x) (wr x)) (wh x)) x)

end CFSG.KC.ModZCode
