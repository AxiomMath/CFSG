module

public import Certificates.Data.Kernel.Spor.ConjTree

public section

namespace CFSG.KS.MulTree

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def ev (w : Nat) (GS PA LA : Nat → Nat) (f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ z => z)
    (fun _ ih i z => Nat.rec (motive := fun _ => Nat) z
      (fun _ _ => pg w (mask w) (GS (LA i)) (ih (PA i) z)) i) f

@[expose] noncomputable def itn (g : Nat → Nat) (k z : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) z (fun _ y => g y) k

end CFSG.KS.MulTree

end
