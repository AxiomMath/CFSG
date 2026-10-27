module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.CommBase
public import CFSG.Mathlib.Decide.Nodup

public section

namespace CFSG.KC.D42T2

open CFSG.KC.Enum CFSG.KC.CommBase

@[expose] noncomputable def orbOK (n : Nat) (f : Nat → Nat → Nat) (k b : Nat) (P Q L : List Nat) :
    Bool :=
  bAnd(Nat.blt b n, bAnd(Nat.beq (P.getD (nat_lit 0) n) b, bAnd(allL (fun p => Nat.blt p n) P,
    bAnd(CFSG.Decide.bitsetNodup P, allN P.length (fun i => bIf(Nat.beq i (nat_lit 0), true,
      bAnd(Nat.blt (Q.getD i (nat_lit 0)) i, bAnd(Nat.blt (L.getD i (nat_lit 0)) k,
        Nat.beq (f (L.getD i (nat_lit 0)) (P.getD (Q.getD i (nat_lit 0)) (nat_lit 0)))
          (P.getD i (nat_lit 0))))))))))

end CFSG.KC.D42T2

end
