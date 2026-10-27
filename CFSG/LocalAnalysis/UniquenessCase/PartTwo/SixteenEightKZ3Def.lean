module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

abbrev S16kGL6 : Type := Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)

def s16kBlockMat (i : Fin 3) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun r c =>
    if r.val / 2 = i.val ∧ c.val / 2 = i.val then
      (if r.val % 2 = 0 then (if c.val % 2 = 1 then 1 else 0) else 1)
    else if r = c then 1 else 0

def s16kDiag : Subgroup S16kGL6 :=
  Subgroup.closure {g | ∃ i : Fin 3, (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = s16kBlockMat i}

def s16kScal : Subgroup S16kGL6 :=
  Subgroup.closure {g | (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
    s16kBlockMat 0 * s16kBlockMat 1 * s16kBlockMat 2}

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
