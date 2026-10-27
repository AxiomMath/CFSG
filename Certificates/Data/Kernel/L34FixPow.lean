module

public import Certificates.Data.Kernel.L34K

public section

namespace CFSG.KC.L34FixPow

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw

@[expose] noncomputable def itK (x k p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) p (fun _ q => pg 6 (mask 6) x q) k

@[expose] noncomputable def fixPow (x k : Nat) : Bool :=
  allN 42 fun p => Nat.beq (itK x k p) p

end CFSG.KC.L34FixPow

end
