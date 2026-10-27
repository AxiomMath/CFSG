module

public import Certificates.Data.Kernel.M24G.StmtB

public section

namespace CFSG.KC.J4DCE

open CFSG.KC.M24G

@[expose] def firstOK (TP TG : IxTree Nat) : List Nat → List Nat → Nat → Bool
  | [], [], _ => true
  | a :: AX, b :: AY, p =>
    (a == 0 || decide (getT TP a < p) || (getT TP a == p && getT TG a == 0)) &&
      (b == 0 || decide (getT TP b ≤ p)) && firstOK TP TG AX AY (p + 1)
  | _, _, _ => false

end CFSG.KC.J4DCE
