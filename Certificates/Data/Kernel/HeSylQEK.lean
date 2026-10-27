module

public import Certificates.Data.Kernel.HeAutK

public section

namespace CFSG.KC.HeAutK

open CFSG.KC.Enum CFSG.KS CFSG.KC.HexaK
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def interK (NE : Nat) (TE : Nat → Nat) (NQ : Nat) (TQ : Nat → Nat)
    (k l : Nat) : Bool :=
  andB (Nat.beq (cntR (fun i => inL NQ TQ (TE i)) (nat_lit 0) NE) k)
    (Nat.beq (cntR (fun i => notB (inL NQ TQ (TE i))) (nat_lit 0) NE) l)

@[expose] noncomputable def centK (n w NX : Nat) (TX : Nat → Nat) (g : Nat) (G : Nat → Nat)
    (z : Nat) : Bool :=
  allN NX fun i => strictB (TX i) fun x =>
    orB (notB (allN g fun k => comm n w x (G k))) (inZ n w z x)

end CFSG.KC.HeAutK

end
