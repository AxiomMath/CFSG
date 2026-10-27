module

public import Certificates.Data.Kernel.LocalQT.HSAutR

public section

namespace CFSG.KS.HSAutO

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.HSAutN

@[expose] noncomputable def po (p q : Nat) : Nat := pcomp (nat_lit 35) (nat_lit 6) (mask 6) p q

@[expose] noncomputable def clPtK (G GI T LAB WIT CP REP : Nat → Nat) (cnt k : Nat) : Bool :=
  strictB (T k) (fun t => strictB (r32 LAB k) (fun l => strictB (r32 WIT k) (fun w =>
  bAnd(Nat.blt l (nat_lit 14), bAnd(Nat.blt w cnt,
  bAnd(Nat.beq (po (T w) (T (r32 REP l))) (po t (T w)),
  allN (nat_lit 2) (fun j => strictB (r32 CP (Nat.add (Nat.mul k (nat_lit 2)) j)) (fun c =>
    bAnd(Nat.blt c cnt, bAnd(Nat.beq (T c) (po (po (G j) t) (GI j)),
      Nat.beq (r32 LAB c) l))))))))))

@[expose] noncomputable def oPtK (G GI T PL POS SRT SRI LAB WIT CP REP : Nat → Nat) (cnt i : Nat) :
    Bool :=
  bAnd(penumPtK (nat_lit 35) (nat_lit 6) (mask 6) (nat_lit 210) false G GI (nat_lit 2) cnt T PL
    POS SRT SRI i, clPtK G GI T LAB WIT CP REP cnt i)

@[expose] noncomputable def cntL (LAB : Nat → Nat) (l lo len : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun d ih => strictN ih (fun a =>
    nIf(Nat.beq (r32 LAB (Nat.add lo d)) l, Nat.succ a, a))) len

@[expose] noncomputable def oSlK (G GI T PL POS SRT SRI LAB WIT CP REP VC : Nat → Nat)
    (cnt s : Nat) : Bool :=
  bAnd(allN (nat_lit 64) (fun d => strictB (Nat.add (Nat.mul s (nat_lit 64)) d) (fun i =>
      oPtK G GI T PL POS SRT SRI LAB WIT CP REP cnt i)),
    allN (nat_lit 14) (fun l => Nat.beq (cntL LAB l (Nat.mul s (nat_lit 64)) (nat_lit 64))
      (r32 VC (Nat.add (Nat.mul s (nat_lit 14)) l))))

@[expose] noncomputable def sumVC (VC : Nat → Nat) (l c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun s ih => strictN ih (fun a =>
    Nat.add a (r32 VC (Nat.add (Nat.mul s (nat_lit 14)) l)))) c

@[expose] noncomputable def repK (LAB REP : Nat → Nat) (cnt : Nat) : Bool :=
  allN (nat_lit 14) (fun l => strictB (r32 REP l) (fun r =>
    bAnd(Nat.blt r cnt, Nat.beq (r32 LAB r) l)))

@[expose] noncomputable def restrK (E G : Nat) (OP : Nat → Nat) : Bool :=
  bAnd(allN (nat_lit 35) (fun i => Nat.beq (img E (r32 OP i))
      (r32 OP (pg (nat_lit 6) (mask 6) G i))),
    bAnd(allN (nat_lit 34) (fun i => Nat.blt (r32 OP i) (r32 OP (Nat.succ i))),
      Nat.blt (r32 OP (nat_lit 34)) (nat_lit 3850)))

@[expose] noncomputable def bitK (M x : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight M x) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def qInvK (E QM : Nat) : Bool :=
  allN (nat_lit 3850) (fun x => bIf(bitK QM x, bitK QM (img E x), true))

end CFSG.KS.HSAutO

end
