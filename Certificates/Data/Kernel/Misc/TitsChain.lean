module

public import Certificates.Data.Kernel.YModel.Text

public section

namespace CFSG.KC.TitsChain

open CFSG.KC.YModel

@[expose] def decIntK (x : Nat) : Int :=
  if x % 2 = 1 then -((x / 2 : Nat) : Int) else ((x / 2 : Nat) : Int)

@[expose] noncomputable def linesWK (n : Nat → Nat) (w : Nat) (F : Nat → Nat) (lines : Nat) :
    List (List Int) :=
  (List.range (lines - 1)).map fun L =>
    (List.range (n (L + 1))).map fun i => decIntK (fieldAt w (F (L + 1)) i)

end CFSG.KC.TitsChain

end
