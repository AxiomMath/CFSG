module

public import Certificates.Data.Kernel.ListBridge

public section

namespace CFSG.KC.ListBridge

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw

@[expose] noncomputable def pcommutK (n w x y : Nat) : Nat :=
  pcomp n w (mask w) (pcomp n w (mask w) (pcomp n w (mask w) x y) (pinvS n w (mask w) x))
    (pinvS n w (mask w) y)

@[expose] noncomputable def commPtsK (n w N : Nat) (T : Nat → Nat) (NB : Nat) (TB : Nat → Nat) :
    Bool :=
  allN N fun i => allN N fun j => inK NB TB (pcommutK n w (T i) (T j))

@[expose] noncomputable def abelPtsK (n w N : Nat) (T : Nat → Nat) : Bool :=
  allN N fun i => allN N fun j =>
    Nat.beq (pcomp n w (mask w) (T i) (T j)) (pcomp n w (mask w) (T j) (T i))

end CFSG.KC.ListBridge

end
