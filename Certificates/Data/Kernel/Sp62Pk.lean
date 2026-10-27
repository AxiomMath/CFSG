module

public import Certificates.Data.Kernel.Misc.G24
public import Certificates.Data.Kernel.G2Three.Defs

public section

namespace CFSG.KD.Sp62

open CFSG.KC.Loop

@[expose] def pk (m : List Nat) : Nat := m.foldr (fun e acc => e + 2 * acc) 0

@[expose] noncomputable def M36 : Nat := 68719476735

@[expose] noncomputable def MULF (A B : Nat) : Nat :=
  Nat.land (CFSG.KC.Misc.G24.mulF2 6 A B) M36

@[expose] noncomputable def ONE : Nat := 34630287489

@[expose] noncomputable def P2K (x k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ y => MULF y y) k

@[expose] noncomputable def P17920 (x : Nat) : Nat :=
  P2K (MULF (MULF (P2K x 5) (MULF x x)) x) 9

@[expose] noncomputable def buildG (st : Nat → Nat → Nat) (X PA PB : Nat → Nat) (n k hi : Nat) :
    Bool :=
  allBelow (Nat.sub n 1) hi fun i =>
    Nat.ble (PA i) i && Nat.blt (PB i) k && Nat.beq (X (Nat.succ i)) (st (X (PA i)) (PB i))

@[expose] noncomputable def stepG (st : Nat → Nat → Nat) (X PA PB C POS : Nat → Nat)
    (n k hi : Nat) : Bool :=
  Nat.beq (C 0) 1 && Nat.beq (C (Nat.mul n k)) n &&
  allBelow (Nat.mul n k) hi fun i =>
    Nat.blt (Nat.div i k) (C i) && Nat.ble (POS i) (C i) && Nat.blt (POS i) n &&
    Nat.beq (X (POS i)) (st (X (Nat.div i k)) (Nat.mod i k)) &&
    cond (Nat.beq (POS i) (C i))
      (Nat.beq (C (Nat.succ i)) (Nat.succ (C i)) && Nat.beq (PA (Nat.pred (C i))) (Nat.div i k) &&
        Nat.beq (PB (Nat.pred (C i))) (Nat.mod i k))
      (Nat.beq (C (Nat.succ i)) (C i))

@[expose] noncomputable def rmulSt (G : Nat → Nat) (x s : Nat) : Nat := MULF x (G s)

@[expose] noncomputable def conjSt (GA GB : Nat → Nat) (x s : Nat) : Nat :=
  MULF (MULF (GA s) x) (GB s)

@[expose] noncomputable def hypF (BC Z0 Z1 Z2 Z0I Z1I Z2I y : Nat) : Bool :=
  !(Nat.beq (MULF y BC) (MULF BC y) && Nat.beq (P17920 y) ONE) || Nat.beq y ONE ||
    (!Nat.beq (P17920 (MULF y (MULF (MULF Z0 y) Z0I))) ONE ||
      !Nat.beq (P17920 (MULF y (MULF (MULF Z1 y) Z1I))) ONE ||
      !Nat.beq (P17920 (MULF y (MULF (MULF Z2 y) Z2I))) ONE)

@[expose] noncomputable def recX (R : Nat → Nat) (o t : Nat) : Nat := Nat.land (R (Nat.add o t)) M36

@[expose] noncomputable def recF (R : Nat → Nat) (o f t : Nat) : Nat :=
  Nat.land (Nat.shiftRight (R (Nat.add o t)) (Nat.add 40 (Nat.mul 16 f))) 65535

@[expose] noncomputable def recC (R : Nat → Nat) (o i : Nat) : Nat :=
  recF R o (Nat.add 4 (Nat.mod i 2)) (Nat.div i 2)

@[expose] noncomputable def recPOS (R : Nat → Nat) (o i : Nat) : Nat :=
  recF R o (Nat.add 6 (Nat.mod i 2)) (Nat.div i 2)

@[expose] noncomputable def at2 (R : Nat → Nat) (a s : Nat) : Nat := R (Nat.add a s)

@[expose] noncomputable def tableK (R : Nat → Nat) (st : Nat → Nat → Nat) (o n hiB hiS hiT : Nat) :
    Bool :=
  buildG st (recX R o) (recF R o 0) (recF R o 1) n 2 hiB &&
    stepG st (recX R o) (recF R o 0) (recF R o 1) (recC R o) (recPOS R o) n 2 hiS &&
    CFSG.KD.G2Three.sortK (recX R o) (recF R o 2) (recF R o 3) n hiT

@[expose] noncomputable def hypK (R : Nat → Nat) (bc o n hi : Nat) : Bool :=
  allBelow n hi fun t =>
    hypF (R bc) (R 27) (R 28) (R 29) (R 30) (R 31) (R 32) (recX R o t)

end CFSG.KD.Sp62

end
