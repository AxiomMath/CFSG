module

public import Certificates.Data.Kernel.B433Alt.Net

public section

namespace CFSG.KC.Y333

@[expose] noncomputable def tagOK (B x : Nat) : Bool :=
  Nat.beq (Nat.shiftRight B (nat_lit 81920)) (Nat.shiftRight x (nat_lit 12))

@[expose] noncomputable def untag (B : Nat) : Nat :=
  Nat.land B (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 81920)) (nat_lit 1))

@[expose] noncomputable def lkTF (R K B x : Nat) : Bool :=
  Bool.rec false (lkF R K (colGet B (colOff x))) (tagOK B x)

@[expose] noncomputable def lkTB (R K B x : Nat) : Bool :=
  Bool.rec false (lkB R K (colGet B (colOff x))) (tagOK B x)

end CFSG.KC.Y333

end
