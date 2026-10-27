module

public import Certificates.Data.Kernel.SporSch.Co1BfsSeg

public section

namespace CFSG.KS.SporSch.M24

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def bfsSegFK (F : Nat → Nat → Nat) (ng cap N : Nat) (P PAR LAB W S : Nat → Nat)
    (K i : Nat) : Bool :=
  strictB (Nat.mul i K) fun h =>
    bAnd(Nat.beq (bfsSegK F P PAR LAB W ng cap K h (cAtK PAR N h))
        (cAtK PAR N (Nat.add h K)), allBlk h (distAtK P S N) K)

@[expose] noncomputable def bfsHeadK (P PAR LAB : Nat → Nat) (N K m R : Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) N, bAnd(Nat.beq (P (nat_lit 0)) R, bAnd(Nat.beq (PAR (nat_lit 0)) (nat_lit 0),
    bAnd(Nat.beq (LAB (nat_lit 0)) (nat_lit 0), bAnd(Nat.beq (cAtK PAR N (nat_lit 0)) (nat_lit 1),
      bAnd(Nat.beq (cAtK PAR N N) N, Nat.beq (Nat.mul m K) N))))))

end CFSG.KS.SporSch.M24

end
