module

public import Certificates.Data.Kernel.Spor.ONPwK

public section

namespace CFSG.KS.ONPw

open CFSG.KC.Enum

@[expose] noncomputable def pathEq (D : Nat → Nat) (r : Nat) : Bool :=
  strictB (fld(D (rB r), nat_lit 19, nat_lit 3)) fun k =>
    bAnd(Nat.ble k r, Nat.beq (D (Nat.succ (rB r))) (D (Nat.succ (rB (Nat.sub r k)))))

end CFSG.KS.ONPw

end
