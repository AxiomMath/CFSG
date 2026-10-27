module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch1413

open Matrix

theorem l33_dec_inner (M : GL (Fin 2) (ZMod 3)) (h2 : M * M = 1) (h1 : M ≠ 1) (hm : M ≠ -1) :
    ∃ N : GL (Fin 2) (ZMod 3), (N * M * N⁻¹ * M⁻¹) ^ 2 = -1 := by
  revert M
  decide +kernel

theorem l33_dec_outer (M : GL (Fin 2) (ZMod 3))
    (hs : (M : Matrix (Fin 2) (Fin 2) (ZMod 3)).transpose = M) :
    ∃ N : GL (Fin 2) (ZMod 3),
      ((N : Matrix (Fin 2) (Fin 2) (ZMod 3)) * (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) *
        (N : Matrix (Fin 2) (Fin 2) (ZMod 3)).transpose *
          ((M⁻¹ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))) ^ 2 = -1 := by
  revert M
  decide +kernel

end CFSG.LocalAnalysis.WeakClosure81.Asch1413

end
