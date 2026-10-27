module

public import Certificates.Data.Kernel.Fi22Gen.Defs

public section

namespace CFSG.KS.Fi22RkInv

open CFSG.KC.Enum CFSG.KS.Fi22Gen

@[expose] noncomputable def ptK (F : Nat → Nat → Nat) (X : Nat → Nat) (s t u : List Nat)
    (b : Nat) : Bool :=
  bAnd(Nat.beq (wAp F s (wAp F s b)) b,
  bAnd(Nat.beq (wAp F s (X (wAp F s (X b)))) b,
  bAnd(Nat.beq (wAp F t (wAp F t b)) b,
  bAnd(Nat.beq (wAp F u (wAp F u b)) b,
  bAnd(Nat.beq (wAp F t (X b)) (X (wAp F t b)),
  bAnd(Nat.beq (wAp F u (X b)) (X (wAp F u b)),
    Nat.beq (wAp F t (wAp F u (wAp F t (wAp F u (wAp F t (wAp F u b)))))) b))))))

@[expose] noncomputable def invK (F : Nat → Nat → Nat) (X : Nat → Nat) (s t u : List Nat)
    (m : Nat) : Bool :=
  bAnd(lettersLt (nat_lit 32) s, bAnd(lettersLt (nat_lit 32) t, bAnd(lettersLt (nat_lit 32) u,
  bAnd(allN (nat_lit 5) fun i => ptK F X s t u (BS i),
  bAnd(Nat.blt m (nat_lit 5), Bool.not (Nat.beq (wAp F t (wAp F u (BS m))) (BS m)))))))

end CFSG.KS.Fi22RkInv

end
