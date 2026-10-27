module

public import Certificates.Data.Kernel.Misc.YamakiRepF
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KD.OmegaSix

open CFSG.KD.BfsK CFSG.KD.YamakiRepF CFSG.KC.Loop
open CFSG.KD.Sp62 (MULF ONE)

@[expose] noncomputable def cjG (R : Nat → Nat) (x s : Nat) : Nat :=
  MULF (MULF (R s) x) (R (Nat.add 2 s))

@[expose] noncomputable def headC (R : Nat → Nat) (o n : Nat) : Bool :=
  bAnd(Nat.beq (recX R o 0) (R 4), bAnd(Nat.beq (recC R o 2 0) 1,
    Nat.beq (recC R o 2 (Nat.mul n 2)) n))

@[expose] noncomputable def hdrC (R : Nat → Nat) (a b x : Nat) : Bool :=
  bAnd(Nat.beq (R 0) a, bAnd(Nat.beq (R 1) b, bAnd(Nat.beq (R 2) a,
    bAnd(Nat.beq (R 3) (MULF b (MULF b (MULF b b))), Nat.beq (R 4) x))))

@[expose] noncomputable def bsK (X S : Nat → Nat) (x f : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => false)
    (fun _ ih lo hi => bIf(Nat.blt lo hi,
      strictY (Nat.shiftRight (Nat.add lo hi) 1) fun m => strictY (X (S m)) fun v =>
        bIf(Nat.beq v x, true, bIf(Nat.blt v x, ih (Nat.succ m) hi, ih lo m)), false)) f

@[expose] noncomputable def memK (R : Nat → Nat) (o n x : Nat) : Bool :=
  bsK (recX R o) (recF R o 2) x 16 0 n

@[expose] noncomputable def clsAt (RA : Nat → Nat) (nA : Nat) (RB : Nat → Nat) (nB x : Nat) :
    Bool :=
  bIf(Nat.beq (MULF x x) ONE, bIf(Nat.beq x ONE, true, bIf(memK RA 5 nA x, true, memK RB 5 nB x)),
    true)

@[expose] noncomputable def clsChunk (R : Nat → Nat) (o n : Nat) (RA : Nat → Nat) (nA : Nat)
    (RB : Nat → Nat) (nB L q : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul L q) L fun t =>
    bIf(Nat.blt t n, strictY (recX R o t) (clsAt RA nA RB nB), true)

@[expose] noncomputable def commN (y x : Nat) : Nat := nIf(Nat.beq (MULF x y) (MULF y x), 1, 0)

@[expose] noncomputable def cntK (R : Nat → Nat) (o n y : Nat) : Nat :=
  sumBelow n (Nat.add (Nat.shiftRight n 6) 1) fun t => strictN (recX R o t) (commN y)

end CFSG.KD.OmegaSix

end
