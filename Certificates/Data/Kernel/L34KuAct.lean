module

public import Certificates.Data.Kernel.L34Scan

public section

namespace CFSG.KC.L34Scan

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def kuK (n w r CN : Nat) (CP : Nat → Nat) (e x : Nat) : Bool :=
  orB (notB (commPt n w x r))
    (orB (notB (allN CN fun c => commPt n w x (pcomp n w (mask w) (CP c) (CP c))))
      (Nat.beq (pow2K n w (nat_lit 5) x) e))

end CFSG.KC.L34Scan

end
