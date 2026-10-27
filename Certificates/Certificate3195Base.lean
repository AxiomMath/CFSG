module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParH1Data

@[expose] public section

open CFSG.EvenSmallLie.UnitarySix.YamadaPar

namespace Certificates

abbrev suClosure : Subgroup (Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :=
  Subgroup.closure {g | (g : Matrix (Fin 8) (Fin 8) (ZMod 2)) = toMat 8 8 (genBits 0) ∨
    (g : Matrix (Fin 8) (Fin 8) (ZMod 2)) = toMat 8 8 (genBits 1)}

end Certificates

