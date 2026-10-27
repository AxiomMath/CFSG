module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KC.SB

open CFSG.KC.Enum

@[expose] noncomputable def sMulG (AR MR : Nat → Nat) (c d : Nat) : Nat :=
  strictN (Nat.land (Nat.shiftRight c (nat_lit 7)) (nat_lit 511)) fun g =>
  strictN (Nat.land d (nat_lit 127)) fun e =>
  strictN (Nat.land (Nat.shiftRight d (nat_lit 7)) (nat_lit 511)) fun h =>
    Nat.add (Nat.xor (Nat.land c (nat_lit 127)) fld(AR g, Nat.mul (nat_lit 7) e, nat_lit 127))
      (Nat.mul (nat_lit 128) fld(MR g, Nat.mul (nat_lit 9) h, nat_lit 511))

@[expose] noncomputable def sInvG (AR : Nat → Nat) (GL c : Nat) : Nat :=
  strictN fld(GL, Nat.mul (nat_lit 9) (Nat.land (Nat.shiftRight c (nat_lit 7)) (nat_lit 511)),
    nat_lit 511) fun gi =>
    Nat.add fld(AR gi, Nat.mul (nat_lit 7) (Nat.land c (nat_lit 127)), nat_lit 127)
      (Nat.mul (nat_lit 128) gi)

@[expose] noncomputable def linG (LL v : Nat) : Nat :=
  nIf(Nat.blt v (nat_lit 512), fld(LL, Nat.mul (nat_lit 16) v, nat_lit 65535), nat_lit 0)

@[expose] noncomputable def coG (CR : Nat → Nat) (c : Nat) : Nat :=
  nIf(Nat.blt c (nat_lit 65536),
    fld(CR (Nat.shiftRight c (nat_lit 7)), Nat.mul (nat_lit 9) (Nat.land c (nat_lit 127)), nat_lit 511),
    nat_lit 0)

@[expose] noncomputable def nfEG (NR : Nat → Nat) (x : Nat) : Nat :=
  nIf(Nat.blt x (nat_lit 65536),
    fld(NR (Nat.shiftRight x (nat_lit 7)), Nat.mul (nat_lit 16) (Nat.land x (nat_lit 127)), nat_lit 127),
    nat_lit 0)

@[expose] noncomputable def nfAG (NR : Nat → Nat) (x : Nat) : Nat :=
  nIf(Nat.blt x (nat_lit 65536),
    fld(NR (Nat.shiftRight x (nat_lit 7)),
      Nat.add (Nat.mul (nat_lit 16) (Nat.land x (nat_lit 127))) (nat_lit 7), nat_lit 511),
    nat_lit 0)

end CFSG.KC.SB

end
