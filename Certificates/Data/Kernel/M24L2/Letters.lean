module

public import Certificates.Data.Kernel.M24L2.Code
public import CFSG.CGT.M24R.L2Data
public import CFSG.CGT.M24R.RelData
public import Mathlib

public section

namespace CFSG.KC.M24L2

open CFSG.Sporadic.Th.Native CFSG.CGT.M24R

@[expose] noncomputable def lcC (l : Fin 10 × Bool) : Nat := codeF fun x => ap (letTab l) x

@[expose] noncomputable def cwK (w : List (Fin 10 × Bool)) : Nat :=
  foldL (fun c l => mulC c (lcC l)) w idC

end CFSG.KC.M24L2
