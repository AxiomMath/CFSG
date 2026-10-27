module

public import Certificates.Data.Kernel.Misc.YamakiRepF
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KD.OmegaSix

open CFSG.KD.BfsK CFSG.KD.YamakiRepF
open CFSG.KD.Sp62 (MULF)

@[expose] noncomputable def cosetAt (RC : Nat → Nat) (oC nC r s₁ s₂ w X : Nat) : Bool :=
  bIf(Nat.beq (MULF X r) (MULF r X), true,
    bAnd(Nat.blt w nC, strictY (MULF (recX RC oC w) X) fun cy => strictY (MULF cy r) fun u =>
      bIf(Nat.beq u (MULF s₁ cy), true, Nat.beq u (MULF s₂ cy))))

@[expose] noncomputable def cosetChunk (R : Nat → Nat) (o n : Nat) (RC : Nat → Nat) (oC nC : Nat)
    (W : Nat → Nat) (r s₁ s₂ L q : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul L q) L fun t =>
    bIf(Nat.blt t n, strictY (recX R o t) (cosetAt RC oC nC r s₁ s₂ (W t)), true)

@[expose] noncomputable def posAt (R : Nat → Nat) (o n p x : Nat) : Bool :=
  bAnd(Nat.blt p n, Nat.beq (recX R o p) x)

end CFSG.KD.OmegaSix

end
