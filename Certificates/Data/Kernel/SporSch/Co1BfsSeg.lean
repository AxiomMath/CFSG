module

public import Certificates.Data.Kernel.SporSch.Co1Bfs

public section

namespace CFSG.KS.SporSch.M24

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def bfsSegK (F : Nat → Nat → Nat) (P PAR LAB W : Nat → Nat) (ng cap k : Nat) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ c => c)
    (fun _ ih h c => nIf(bAnd(Nat.blt h c, Nat.blt c cap),
      strictN (bfsRowK F P PAR LAB W ng h ng (nat_lit 0) c) fun c' =>
        nIf(Nat.beq c' (nat_lit 0), nat_lit 0, ih (Nat.succ h) c'), nat_lit 0)) k

@[expose] noncomputable def cBsK (PAR : Nat → Nat) (h fuel : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun lo _ => lo)
    (fun _ ih lo hi => nIf(Nat.blt lo hi,
      strictN (Nat.shiftRight (Nat.add lo hi) (nat_lit 1)) fun m =>
        nIf(Nat.blt (PAR m) h, ih (Nat.succ m) hi, ih lo m), lo)) fuel

@[expose] noncomputable def cAtK (PAR : Nat → Nat) (N h : Nat) : Nat :=
  cBsK PAR h (nat_lit 64) (nat_lit 1) N

@[expose] noncomputable def distAtK (P S : Nat → Nat) (N k : Nat) : Bool :=
  bAnd(Nat.blt (S k) N, bAnd(Nat.blt (P k) (Nat.shiftLeft (nat_lit 1) (nat_lit 576)),
    bIf(Nat.beq (Nat.succ k) N, true, Nat.blt (P (S k)) (P (S (Nat.succ k))))))

@[expose] noncomputable def gtSegK (GM : Nat → Nat) (ng cap N : Nat) (P PAR LAB W S : Nat → Nat)
    (K i : Nat) : Bool :=
  strictB (Nat.mul i K) fun h =>
    bAnd(Nat.beq (bfsSegK (gtStepK GM) P PAR LAB W ng cap K h (cAtK PAR N h))
        (cAtK PAR N (Nat.add h K)), allBlk h (distAtK P S N) K)

@[expose] noncomputable def gtHeadK (P PAR LAB : Nat → Nat) (N K m : Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) N, bAnd(Nat.beq (P (nat_lit 0)) idM, bAnd(Nat.beq (PAR (nat_lit 0)) (nat_lit 0),
    bAnd(Nat.beq (LAB (nat_lit 0)) (nat_lit 0), bAnd(Nat.beq (cAtK PAR N (nat_lit 0)) (nat_lit 1),
      bAnd(Nat.beq (cAtK PAR N N) N, Nat.beq (Nat.mul m K) N))))))

end CFSG.KS.SporSch.M24

end
