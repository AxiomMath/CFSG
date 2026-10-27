module

public import Certificates.Data.Kernel.Spor.CommBase

public section

namespace CFSG.KC.CommBase

open CFSG.KC.Enum

@[expose] noncomputable def rootOK (n w m PF RF : Nat) : Bool :=
  allN n (fun p => strictB (pg w m PF p) (fun q =>
    bIf(Nat.beq q p, Nat.beq (pg w m RF p) p, Nat.beq (pg w m RF p) (pg w m RF q))))

@[expose] noncomputable def distOK (B : List BaseRec) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r rs ih => bAnd(allL (fun s : BaseRec => notB (Nat.beq r.1 s.1)) rs, ih)) B

@[expose] noncomputable def memL (v : Nat) (Ts : List Nat) : Bool :=
  anyL (fun t => Nat.beq t v) Ts

@[expose] noncomputable def chooseL (r : BaseRec) (f : Nat → Bool) : Bool :=
  bAnd(f r.1, bIf(Nat.beq r.2.2.2.2 r.1, allL (fun s : Nat × List Nat => f s.1) r.2.2.2.1,
    f r.2.2.2.2))

@[expose] noncomputable def cntR (n w m RF b : Nat) : Nat :=
  CFSG.KC.Loop.sumBelow n (Nat.add (Nat.shiftRight n 6) 1)
    (fun p => nIf(Nat.beq (pg w m RF p) b, 1, 0))

@[expose] noncomputable def fixCnt (n w m P : Nat) : Nat :=
  CFSG.KC.Loop.sumBelow n (Nat.add (Nat.shiftRight n 6) 1)
    (fun p => nIf(Nat.beq (pg w m P p) p, 1, 0))

@[expose] noncomputable def enumOK (n w m t RF : Nat) (Ts : List Nat) (rs : List BaseRec) :
    Nat → Nat → Bool → Bool → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool → Bool → Bool)
    (fun fa fb aA aB => bIf(aA, true, bIf(aB, true, notB (bAnd(memL fa Ts, memL fb Ts)))))
    (fun r _ ih fa fb aA aB => strictB (cntR n w m RF r.1) (fun c => chooseL r (fun y =>
      ih (Nat.add fa (nIf(Nat.beq y r.1, c, 0)))
        (Nat.add fb (nIf(Nat.beq (pg w m t y) r.1, c, 0)))
        (bAnd(aA, Nat.beq y r.1)) (bAnd(aB, Nat.beq (pg w m t y) r.1))))) rs

@[expose] noncomputable def centFixOK (n w m : Nat) (L : Nat → Nat) (nL tI : Nat)
    (B : List BaseRec) (PF ZF DF RF : Nat) (Ts : List Nat) : Bool :=
  bAnd(commBaseOK n w m L nL B PF ZF DF, bAnd(Nat.blt tI nL,
  bAnd(rootOK n w m PF RF, bAnd(distOK B, enumOK n w m (L tI) RF Ts B 0 0 true true))))

end CFSG.KC.CommBase

end
