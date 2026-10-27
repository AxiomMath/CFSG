module

public import Certificates.Data.Kernel.Spor.BfsL

public section

namespace CFSG.KS.SubOrb

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def subOrbK (m k : Nat) (CNT : Nat → Nat) (PT : Nat → Nat → Nat)
    (LB PSN : Nat → Nat) : Bool :=
  bAnd(allN m (fun p => bAnd(Nat.blt (LB p) k, bAnd(Nat.blt (PSN p) (CNT (LB p)),
      Nat.beq (PT (LB p) (PSN p)) p))),
    allN k (fun i => bAnd(Nat.blt (nat_lit 0) (CNT i),
      bAnd(allN (CNT i) (fun q => bAnd(Nat.blt (PT i q) m, Nat.beq (LB (PT i q)) i)),
        allN (PT i (nat_lit 0)) (fun p => Nat.blt (LB p) i)))))

end CFSG.KS.SubOrb

end
