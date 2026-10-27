module

public import Certificates.Data.Kernel.BfsPin
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.ListBridge

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw

@[expose] noncomputable def rPar (r : Nat) : Nat := Nat.land r (nat_lit 65535)

@[expose] noncomputable def rGen (r : Nat) : Nat := Nat.land (Nat.shiftRight r (nat_lit 16)) (nat_lit 255)

@[expose] noncomputable def rDep (r : Nat) : Nat := Nat.shiftRight r (nat_lit 24)

@[expose] noncomputable def depthK (n w ng : Nat) (G T : Nat → Nat) (N fuel : Nat)
    (D : Nat → Nat) : Bool :=
  bAnd(Nat.beq (rDep (D (nat_lit 0))) (nat_lit 0),
    allN N fun i => bIf(Nat.beq i (nat_lit 0), true, strictB (D i) fun r =>
      bAnd(Nat.blt (rPar r) N, bAnd(Nat.blt (rGen r) ng,
        bAnd(Nat.blt (rDep r) (Nat.succ fuel),
          bAnd(Nat.beq (rDep r) (Nat.succ (rDep (D (rPar r)))),
            Nat.beq (T i) (pcomp n w (mask w) (G (rGen r)) (T (rPar r)))))))))

end CFSG.KC.ListBridge

end
