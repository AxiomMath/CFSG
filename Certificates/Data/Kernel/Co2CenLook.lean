module

public import Certificates.Data.Kernel.Co2Cen

public section

namespace CFSG.KC.Co2Cen

open CFSG.KC.Loop CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.Co2Cls CFSG.KC.Co2J CFSG.KC.M1F2
  CFSG.KLie.CT

@[expose] noncomputable def lookC (CF : Nat → Nat → Nat) (NC : Nat → Nat) (X r cls : Nat) : Bool :=
  letB (Nat.land r (nat_lit 15)) fun c => letB (Nat.shiftRight r (nat_lit 4)) fun i =>
    andK (bit cls c) (andK (Nat.blt i (NC c)) (Nat.beq (elemAt (CF c) i) X))

end CFSG.KC.Co2Cen

end
