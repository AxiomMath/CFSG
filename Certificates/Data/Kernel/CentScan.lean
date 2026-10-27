module

public import Certificates.Data.Kernel.L34K

public section

namespace CFSG.KC.CentScan

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.KLie.CT (orB notB)

@[expose] noncomputable def centIdK (n w CN : Nat) (CP : Nat → Nat) (e x : Nat) : Bool :=
  orB (notB (allN CN fun c => commPt n w x (CP c))) (Nat.beq x e)

@[expose] noncomputable def offK (n w CN : Nat) (CP : Nat → Nat) (s x : Nat) : Bool :=
  notB (allN CN fun c => commPt n w (pcomp n w (mask w) s x) (CP c))

end CFSG.KC.CentScan

end
