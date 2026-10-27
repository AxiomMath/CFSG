module

public import Certificates.Data.Kernel.O8.SA

public section

namespace CFSG.KC.O8

open CFSG.KC.Enum

@[expose] noncomputable def actsMK (NS NI P M : Nat) : Bool :=
  allN (nat_lit 136) fun p => strictB (pg (nat_lit 8) (nat_lit 255) P p) fun x =>
    bAnd(Nat.blt x (nat_lit 136), Nat.beq x (pg (nat_lit 8) (nat_lit 255) NI
      (matAppK M (pg (nat_lit 8) (nat_lit 255) NS p))))

@[expose] noncomputable def saClosedAtG (k SC MT GT i : Nat) : Bool :=
  strictB (saAtK SC i) fun x => allN k fun l =>
    Nat.beq (matMulK (saAtK SC (ix13 GT l)) x)
      (saAtK SC (ix13 MT (Nat.add (Nat.mul k i) l)))

@[expose] noncomputable def saTreeAtG (k MT PT LT i : Nat) : Bool :=
  bIf(Nat.beq i (nat_lit 0), true,
    strictB (ix13 PT i) fun p => strictB (fld(LT, Nat.mul (nat_lit 3) i, nat_lit 7)) fun l =>
      bAnd(Nat.blt p i, bAnd(Nat.blt l k,
        Nat.beq (ix13 MT (Nat.add (Nat.mul k p) l)) i)))

@[expose] noncomputable def involAtG (nj SC YI WT i : Nat) : Bool :=
  strictB (saAtK SC i) fun x =>
  bIf(bAnd(bIf(Nat.beq i (nat_lit 0), false, true), Nat.beq (matMulK x x) idK),
    strictB (fld(WT, Nat.add (Nat.mul (nat_lit 32) i) (nat_lit 26), nat_lit 63)) fun j =>
    strictB (fld(WT, Nat.add (Nat.mul (nat_lit 32) i) (nat_lit 13), nat_lit 8191)) fun c =>
    strictB (fld(WT, Nat.mul (nat_lit 32) i, nat_lit 8191)) fun ci =>
      bAnd(Nat.blt j nj, bAnd(Nat.blt c (nat_lit 8192), bAnd(Nat.blt ci (nat_lit 8192),
      bAnd(Nat.beq (matMulK (saAtK SC c) (saAtK SC ci)) idK,
        Nat.beq (matMulK (matMulK (saAtK SC c) (saAtK SC (ix13 YI j))) (saAtK SC ci)) x)))),
    true)

end CFSG.KC.O8

end
