module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.SporSch.PairJ3Cnt
public import Mathlib.Data.Nat.Factorial.Basic

public section

namespace CFSG.KC.TcF

open CFSG.KC.Enum CFSG.KS.SporSch

@[expose] noncomputable def memF (bs : List Nat) (N : Nat) (t : Nat → Nat → Nat) (f : Nat → Nat) :
    Bool :=
  bIf(allN N fun i => bIf(eqOnL bs (t i) f, false, true), false, true)

@[expose] noncomputable def tcRestF (bs : List Nat) (m : Nat) (xf : Nat → Nat) (ngQ : Nat)
    (gQ cu cv cui cvi : Nat → Nat → Nat) (ngK : Nat) (gK : Nat → Nat → Nat)
    (R Ri : Nat → Nat → Nat) (sig : Nat → Nat → Nat) (NQ : Nat) (tq : Nat → Nat → Nat)
    (NK : Nat) (tk : Nat → Nat → Nat) (NS : Nat) : Bool :=
  bAnd(Nat.beq NQ (3 * (Nat.factorial m / 2)),
  bAnd(eqOnL bs (powF xf 3) (fun y => y),
  bAnd(bIf(eqOnL bs xf (fun y => y), false, true),
  bAnd(allN ngQ (fun i => eqOnL bs (fun y => gQ i (xf y)) (fun y => xf (gQ i y))),
  bAnd(memF bs NQ tq xf,
  bAnd(Nat.beq (NK * m) NQ,
  bAnd(memF bs NK tk xf,
  bAnd(allN ngK (fun l => memF bs NQ tq (gK l)),
  bAnd(allN m (fun j => memF bs NQ tq (R j)),
  bAnd(allN m (fun j => allN m fun k => bIf(Nat.beq j k, true,
    bIf(memF bs NK tk (fun y => Ri j (R k y)), false, true))),
  bAnd(allN ngQ (fun i => bAnd(memF bs NQ tq (cu i), bAnd(memF bs NQ tq (cv i),
    eqOnL bs (gQ i) (fun y => cu i (cv i (cui i (cvi i y))))))),
  bAnd(allN ngQ (fun i => allN m fun j => bAnd(Nat.blt (sig i j) m,
    memF bs NK tk (fun y => Ri (sig i j) (gQ i (R j y))))),
    Nat.beq NS (Nat.factorial m / 2)))))))))))))

end CFSG.KC.TcF

end
