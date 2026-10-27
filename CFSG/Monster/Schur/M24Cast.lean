module

public import Certificates.Certificate9250

public section

namespace CFSG.Monster.Schur.M24

open TauCeti

theorem generatorCount_eq : pres.generatorCount = 2 := by
  exact Certificates.certificate9250

@[expose] def idx : Fin 2 → Fin pres.generatorCount :=
  Fin.cast generatorCount_eq.symm

@[expose] def castTo (w : List (Fin 2 × Bool)) :
    List (Fin pres.generatorCount × Bool) :=
  w.map fun x => (idx x.1, x.2)

end CFSG.Monster.Schur.M24
