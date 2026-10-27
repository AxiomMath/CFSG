module

public import Certificates.Data.Kernel.SporCov.BaseKit

public section

namespace CFSG.KC.SporCov

open CFSG.KC.Loop

@[expose] noncomputable def fixB (fA fAi fB fBi : Nat → Nat) (m hi : Nat) (w : List Nat) : Nat :=
  sumBelow m hi fun x => nIf(Nat.beq (imB fA fAi fB fBi w x) x, 1, 0)

@[expose] noncomputable def agB (f g : Nat → Nat) (m hi : Nat) : Bool :=
  allBelow m hi fun x => Nat.beq (f x) (g x)

@[expose] noncomputable def invB (f g : Nat → Nat) (m hi : Nat) : Bool :=
  allBelow m hi fun x => Nat.beq (g (f x)) x

end CFSG.KC.SporCov

end
