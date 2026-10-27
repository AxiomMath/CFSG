module

public import Certificates.Data.Kernel.LocalQT.TcP

public section

namespace CFSG.KC.B45P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.LQT.TC

@[expose] noncomputable def tGenK (n w : Nat) (G GI : List Nat) (T TI S : Nat) (wd : List Int) :
    Bool :=
  bAnd(idK n w (mask w), bAnd(gensTc n w G GI, bAnd(permOK n w (mask w) (n * w) T TI,
    wordP n w (pidn n w) G GI wd fun A _ =>
      bAnd(Nat.beq A S, Nat.beq (pcomp n w (mask w) A T) (pcomp n w (mask w) T A)))))

end CFSG.KC.B45P

end
