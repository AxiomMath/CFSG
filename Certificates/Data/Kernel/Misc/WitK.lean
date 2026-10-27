module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.WitK

open CFSG.KC.Enum (pcomp pidn)
open CFSG.KS (mask)

@[expose] noncomputable def witK (n w P Q Z : Nat) : Bool :=
  Nat.beq (pcomp n w (mask w) P (pcomp n w (mask w) P P)) (pidn n w) &&
    Nat.beq (pcomp n w (mask w) Q (pcomp n w (mask w) Q Q)) (pidn n w) &&
    Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) P Q) (pcomp n w (mask w) P Q)) (pidn n w) &&
    !Nat.beq (pcomp n w (mask w) P Q) (pidn n w) && !Nat.beq (pcomp n w (mask w) P Q) Z

end CFSG.KC.WitK

end
