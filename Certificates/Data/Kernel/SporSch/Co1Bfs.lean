module

public import Certificates.Data.Kernel.SporSch.Co1Mat
public import Certificates.Data.Kernel.Co1BW

public section

namespace CFSG.KS.SporSch.M24

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def bfsRowK (F : Nat → Nat → Nat) (P PAR LAB W : Nat → Nat) (ng h k : Nat) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ c => c)
    (fun _ ih l c => strictN (W (Nat.add (Nat.mul h ng) l)) fun w => strictN (F (P h) l) fun y =>
      nIf(Nat.blt w c, nIf(Nat.beq (P w) y, ih (Nat.succ l) c, nat_lit 0),
        nIf(bAnd(Nat.beq w c, bAnd(Nat.beq (P c) y, bAnd(Nat.beq (PAR c) h, Nat.beq (LAB c) l))),
          ih (Nat.succ l) (Nat.succ c), nat_lit 0))) k

@[expose] noncomputable def bfsRunK (F : Nat → Nat → Nat) (P PAR LAB W : Nat → Nat) (ng cap fuel : Nat) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun _ ih h c => nIf(bAnd(Nat.blt h c, Nat.blt c cap),
      strictN (bfsRowK F P PAR LAB W ng h ng (nat_lit 0) c) fun c' =>
        nIf(Nat.beq c' (nat_lit 0), nat_lit 0, ih (Nat.succ h) c'), c)) fuel

@[expose] noncomputable def bfsDistK (P S : Nat → Nat) (N : Nat) : Bool :=
  allN N fun k => bAnd(Nat.blt (S k) N, bAnd(Nat.blt (P k) (Nat.shiftLeft (nat_lit 1) (nat_lit 576)),
    bIf(Nat.beq (Nat.succ k) N, true, Nat.blt (P (S k)) (P (S (Nat.succ k))))))

@[expose] noncomputable def bfsK (F : Nat → Nat → Nat) (P PAR LAB W S : Nat → Nat) (ng cap N R : Nat) :
    Bool :=
  bAnd(Nat.blt (nat_lit 0) N, bAnd(Nat.beq (P (nat_lit 0)) R, bAnd(Nat.beq (PAR (nat_lit 0)) (nat_lit 0),
    bAnd(Nat.beq (LAB (nat_lit 0)) (nat_lit 0), bAnd(bfsDistK P S N,
      Nat.beq (bfsRunK F P PAR LAB W ng cap (Nat.succ N) (nat_lit 0) (nat_lit 1)) N)))))

@[expose] noncomputable def gtStepK (GM : Nat → Nat) (x l : Nat) : Nat := CFSG.KC.Co1B.mulWK x (GM l)

@[expose] noncomputable def ctStepK (GM GIM : Nat → Nat) (x l : Nat) : Nat :=
  CFSG.KC.Co1B.mulWK (CFSG.KC.Co1B.mulWK (GM l) x) (GIM l)

@[expose] noncomputable def gtClosK (GM P W : Nat → Nat) (ng N : Nat) : Bool :=
  allN N fun h => allN ng fun l => strictB (W (Nat.add (Nat.mul h ng) l)) fun w =>
    bAnd(Nat.blt w N, Nat.beq (P w) (gtStepK GM (P h) l))

@[expose] noncomputable def gtPinK (GM : Nat → Nat) (ng cap N : Nat) (P PAR LAB W S : Nat → Nat) : Bool :=
  bAnd(bfsK (gtStepK GM) P PAR LAB W S ng cap N idM, gtClosK GM P W ng N)

@[expose] noncomputable def ctPinK (GM GIM : Nat → Nat) (R ng cap N : Nat) (P PAR LAB W S : Nat → Nat) :
    Bool :=
  bAnd(Nat.ble cap N, bfsK (ctStepK GM GIM) P PAR LAB W S ng cap N R)

@[expose] noncomputable def bsK (P S : Nat → Nat) (K fuel : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => Nat.shiftLeft (nat_lit 1) (nat_lit 64))
    (fun _ ih lo hi => nIf(Nat.blt lo hi,
      strictN (Nat.shiftRight (Nat.add lo hi) (nat_lit 1)) fun m => strictN (P (S m)) fun v =>
        nIf(Nat.beq v K, S m, nIf(Nat.blt v K, ih (Nat.succ m) hi, ih lo m)),
      Nat.shiftLeft (nat_lit 1) (nat_lit 64))) fuel

@[expose] noncomputable def bfsPosK (P S : Nat → Nat) (N K : Nat) : Nat := bsK P S K (nat_lit 64) (nat_lit 0) N

@[expose] noncomputable def bfsMemK (P S : Nat → Nat) (N K : Nat) : Bool :=
  strictB (bfsPosK P S N K) fun w => bAnd(Nat.blt w N, Nat.beq (P w) K)

end CFSG.KS.SporSch.M24

end
