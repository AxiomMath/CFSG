module

public import Certificates.Data.Kernel.SporSch.ZOrbK

public section

namespace CFSG.KS.SporSch.MBT

open CFSG.KC.Enum CFSG.KS CFSG.KS.M11 CFSG.KS.MEnum CFSG.KS.SporSch.MOC

@[expose] noncomputable def clsSrtK (nw : Nat) (d : ClsD) (k : Nat) : Bool :=
  bIf(Nat.blt k d.c, strictB (d.ST k) (fun x =>
    bAnd(bIf(Nat.blt (Nat.succ k) d.c, Nat.blt x (d.ST (Nat.succ k)), true),
      Nat.beq (Nat.shiftRight x nw) (nat_lit 0))), true)

@[expose] noncomputable def zRepTreeK (n w m A Ai B Bi Z Zi : Nat) (RP OT : Nat → Nat) (d : ClsD)
    (j : Nat) : Bool :=
  strictB (d.PA j) (fun p => bAnd(Nat.blt p d.c,
    bAnd(bIf(Nat.beq (d.LB j) (nat_lit 2), Nat.beq p d.r,
        Nat.blt (d.DP (pg (nat_lit 16) (nat_lit 65535) (OT p) (nat_lit 1))) (d.DP j)),
      Nat.beq (fpow (fun Y => nIf(Nat.beq (d.IB j) (nat_lit 0), conjK n w m Z Zi Y,
          conjK n w m Zi Z Y)) (d.IA j)
        (nIf(Nat.beq (d.LB j) (nat_lit 0), conjK n w m A Ai (d.ST p),
          nIf(Nat.beq (d.LB j) (nat_lit 1), conjK n w m B Bi (d.ST p), d.ST p))))
        (d.ST (RP j)))))

end CFSG.KS.SporSch.MBT

end
