module

public import Certificates.Data.Kernel.Sp6Insp443.Cent

public section

namespace CFSG.KS.Sp6I

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def patK (nw : Nat) (S : Nat → Nat) (c m g : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun r ih =>
    Nat.add ih (nIf(memPK nw (S r) c g, Nat.shiftLeft (nat_lit 1) r, nat_lit 0))) m

end CFSG.KS.Sp6I

end
