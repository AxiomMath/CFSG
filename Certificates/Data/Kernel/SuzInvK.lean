module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.SuzInvK

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def invK (C S T U : Nat) : Bool :=
  Nat.beq (pcomp 1782 11 (mask 11) S S) (pidn 1782 11) &&
    Nat.beq (pcomp 1782 11 (mask 11) (pcomp 1782 11 (mask 11) S C)
      (pcomp 1782 11 (mask 11) S C)) (pidn 1782 11) &&
    Nat.beq (pcomp 1782 11 (mask 11) T T) (pidn 1782 11) &&
    Nat.beq (pcomp 1782 11 (mask 11) U U) (pidn 1782 11) &&
    Nat.beq (pcomp 1782 11 (mask 11) T C) (pcomp 1782 11 (mask 11) C T) &&
    Nat.beq (pcomp 1782 11 (mask 11) U C) (pcomp 1782 11 (mask 11) C U) &&
    Nat.beq (ppow 1782 11 (mask 11) (pidn 1782 11) (pcomp 1782 11 (mask 11) T U) 3)
      (pidn 1782 11) &&
    !Nat.beq (pcomp 1782 11 (mask 11) T U) (pidn 1782 11)

end CFSG.KC.SuzInvK
