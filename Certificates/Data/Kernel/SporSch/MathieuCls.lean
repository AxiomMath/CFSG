module

public import Certificates.Data.Kernel.Spor.Raw
public import Certificates.Data.Kernel.Spor.M11
public import Certificates.Data.Kernel.Spor.MEnum

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.M11 CFSG.KS.MEnum

structure ClsD where
  R : Nat
  c : Nat
  r : Nat
  ST : Nat → Nat
  IA : Nat → Nat
  IB : Nat → Nat
  PA : Nat → Nat
  LB : Nat → Nat
  DP : Nat → Nat

@[expose] noncomputable def clsElemK (n w m nw A Ai B Bi : Nat) (d : ClsD) (k : Nat) : Bool :=
  bIf(Nat.blt k d.c, strictB (d.ST k) (fun x =>
    bAnd(bIf(Nat.blt (Nat.succ k) d.c, Nat.blt x (d.ST (Nat.succ k)), true),
    bAnd(Nat.beq (Nat.shiftRight x nw) (nat_lit 0),
    bAnd(Nat.blt (d.IA k) d.c, bAnd(Nat.beq (conjK n w m A Ai x) (d.ST (d.IA k)),
    bAnd(Nat.blt (d.IB k) d.c, bAnd(Nat.beq (conjK n w m B Bi x) (d.ST (d.IB k)),
    bIf(Nat.beq k d.r, Nat.beq (d.DP k) (nat_lit 0),
      bAnd(Nat.blt (d.PA k) d.c, bAnd(Nat.blt (d.DP (d.PA k)) (d.DP k),
        Nat.beq x (nIf(Nat.beq (d.LB k) (nat_lit 0), conjK n w m A Ai (d.ST (d.PA k)),
          conjK n w m B Bi (d.ST (d.PA k))
        )))))))))))), true)

@[expose] noncomputable def clsHdK (n w m : Nat) (mx cap : Nat) (d : ClsD) : Bool :=
  bAnd(Nat.blt (nat_lit 0) d.c, bAnd(Nat.ble d.c cap, bAnd(Nat.blt d.r d.c,
    bAnd(Nat.beq (d.ST d.r) d.R, Nat.beq (ordC n w m d.R) mx))))

@[expose] noncomputable def notInK (d : ClsD) (x : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => bAnd(bIf(Nat.beq (d.ST k) x, false, true), ih))
    d.c

end CFSG.KS.SporSch.MOC

end
