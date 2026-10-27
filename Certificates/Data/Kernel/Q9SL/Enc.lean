module

public import CFSG.GH74.GLS.Stage4.Q9.TablesInputs
public import Certificates.Data.Kernel.Q9SL.Defs

public section

namespace CFSG.KC.Q9SL

open CFSG.GH74.GLS.Stage4.Q9

@[expose] def eF (a : F9) : Nat := Nat.add (Nat.mul 3 a.re.val) a.im.val

@[expose] noncomputable def enc (M : SL2) : Nat :=
  pk (eF ((M : Matrix (Fin 2) (Fin 2) F9) 0 0)) (eF ((M : Matrix (Fin 2) (Fin 2) F9) 0 1))
    (eF ((M : Matrix (Fin 2) (Fin 2) F9) 1 0)) (eF ((M : Matrix (Fin 2) (Fin 2) F9) 1 1))

end CFSG.KC.Q9SL
