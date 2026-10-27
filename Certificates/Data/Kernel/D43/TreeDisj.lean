module

public import Certificates.Data.Kernel.D43.Tree

public section

namespace CFSG.KC.D43

open CFSG.KC.Enum

@[expose] noncomputable def disjChk (Ra : Nat → Nat) (oa : Nat) (Rb Qb : Nat → Nat)
    (ℓb ob sb t : Nat) : Bool :=
  strictB (ptAt Ra oa t) fun pt => strictB (posAt Qb ℓb pt) fun u =>
    bIf(Nat.blt u sb, bIf(Nat.beq (ptAt Rb ob u) pt, false, true), true)

@[expose] noncomputable def disjChunk (Ra : Nat → Nat) (oa sa : Nat) (Rb Qb : Nat → Nat)
    (ℓb ob sb c : Nat) : Bool :=
  allBlk (Nat.mul (nat_lit 256) c)
    (fun t => bIf(Nat.blt t sa, disjChk Ra oa Rb Qb ℓb ob sb t, true)) (nat_lit 256)

end CFSG.KC.D43
