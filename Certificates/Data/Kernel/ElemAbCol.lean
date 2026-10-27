module

public import Certificates.Data.Kernel.Census.Packed

public section

namespace CFSG.KC.ElemAbCol

open CFSG.KC.Census

@[expose] noncomputable def ncPw (n w : Nat) : List Nat → Bool
  | [] => true
  | a :: l => l.all (fun b => !pcommA n w a b) && ncPw n w l

@[expose] noncomputable def covd (n w : Nat) (cls : List (List Nat)) (x : Nat) : Bool :=
  Nat.beq x (pid n w) || !Nat.beq (pc n w x x) (pid n w) || cls.any fun l => l.any (Nat.beq x)

@[expose] noncomputable def colOK (n w K : Nat) (pts : List Nat) (cls : List (List Nat)) : Bool :=
  Nat.ble cls.length K && cls.all (ncPw n w) && pts.all (covd n w cls)

end CFSG.KC.ElemAbCol
