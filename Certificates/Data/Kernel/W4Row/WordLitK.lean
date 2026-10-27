module

public import Certificates.Data.Kernel.LocalQT.Tc

public section

namespace CFSG.KC.W4E

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.LQT.TC

@[expose] noncomputable def wordLitK (n w : Nat) (G GI : List Nat) (wd : List Int) (Y YI : Nat) :
    Bool :=
  bAnd(Nat.beq (wordTc n w (pidn n w) G GI wd) Y, permOK n w (mask w) (n * w) Y YI)

end CFSG.KC.W4E

end
