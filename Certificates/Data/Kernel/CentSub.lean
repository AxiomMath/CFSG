module

public import Certificates.Data.Kernel.L34K

public section

namespace CFSG.KC.CentSub

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.KLie.CT (orB notB)

@[expose] noncomputable def centSubK (n w CN : Nat) (CP : Nat → Nat) (ZN : Nat) (ZP : Nat → Nat)
    (x : Nat) : Bool :=
  orB (notB (allN CN fun c => commPt n w x (CP c)))
    (notB (allN ZN fun k => notB (Nat.beq x (ZP k))))

end CFSG.KC.CentSub

end
