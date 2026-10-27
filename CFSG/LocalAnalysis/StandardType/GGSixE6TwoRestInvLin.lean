module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestInvLinK

public section

namespace CFSG.StandardType.GGSixE6Two

abbrev e6TwoRestQV : Type := Fin 16 → ZMod 2

@[expose] def invMat : Fin 14 → Matrix (Fin 16) (Fin 16) (ZMod 2) :=
  ![!![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    !![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    !![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    !![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1],
    !![1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

@[expose] def invU1 : Submodule (ZMod 2) e6TwoRestQV where
  carrier := {v | ∀ i : Fin 16, 8 ≤ (i : ℕ) → v i = 0}
  add_mem' := fun ha hb i hi => by simp [ha i hi, hb i hi]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c v hv i hi => by simp [hv i hi]

@[expose] def invU2 : Submodule (ZMod 2) e6TwoRestQV where
  carrier := {v | ∀ i : Fin 16, (i : ℕ) < 8 → v i = 0}
  add_mem' := fun ha hb i hi => by simp [ha i hi, hb i hi]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c v hv i hi => by simp [hv i hi]

@[expose] def e6il_applyWord : List (Fin 14) → e6TwoRestQV → e6TwoRestQV
  | [], v => v
  | k :: w, v => e6il_applyWord w ((invMat k).mulVec v)

theorem e6il_applyWord_cons (k : Fin 14) (w : List (Fin 14)) (v : e6TwoRestQV) :
    e6il_applyWord (k :: w) v = e6il_applyWord w ((invMat k).mulVec v) := rfl

theorem e6il_applyWord_mem {W : Submodule (ZMod 2) e6TwoRestQV}
    (hW : ∀ k : Fin 14, ∀ v ∈ W, (invMat k).mulVec v ∈ W) (w : List (Fin 14)) :
    ∀ v : e6TwoRestQV, v ∈ W → e6il_applyWord w v ∈ W := by
  induction w with
  | nil => intro v hv; exact hv
  | cons k w ih =>
      intro v hv
      rw [e6il_applyWord_cons]
      exact ih _ (hW k v hv)

@[expose] def e6il_incl (k : Fin 8) : Fin 16 := ⟨k.1, by omega⟩

@[expose] def e6il_incl8 (k : Fin 8) : Fin 16 := ⟨k.1 + 8, by omega⟩

@[expose] def e6il_vb (b0 b1 b2 b3 b4 b5 b6 b7 : Fin 2) : e6TwoRestQV :=
  ![b0, b1, b2, b3, b4, b5, b6, b7, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def e6il_wb (b0 b1 b2 b3 b4 b5 b6 b7 : Fin 2) : e6TwoRestQV :=
  ![0, 0, 0, 0, 0, 0, 0, 0, b0, b1, b2, b3, b4, b5, b6, b7]

@[expose] def e6il_bit (v : e6TwoRestQV) (k : Fin 8) : Fin 2 := if v (e6il_incl k) = 0 then 0 else 1

@[expose] def e6il_bit2 (v : e6TwoRestQV) (k : Fin 8) : Fin 2 := if v (e6il_incl8 k) = 0 then 0 else 1

theorem e6il_zmod2_bit (x : ZMod 2) : (if x = 0 then (0 : ZMod 2) else 1) = x := by
  fin_cases x <;> rfl

@[expose] def e6il_e (k : Fin 8) : e6TwoRestQV := Pi.single (e6il_incl k) (1 : ZMod 2)

@[expose] def e6il_f (k : Fin 8) : e6TwoRestQV := Pi.single (e6il_incl8 k) (1 : ZMod 2)

@[expose] def e6il_idxNat1 (v : e6TwoRestQV) : ℕ :=
  ∑ k : Fin 8, (if v (e6il_incl k) = 0 then 0 else 1) * 2 ^ (k : ℕ)

@[expose] def e6il_idxNat2 (v : e6TwoRestQV) : ℕ :=
  ∑ k : Fin 8, (if v (e6il_incl8 k) = 0 then 0 else 1) * 2 ^ (k : ℕ)

@[expose] def e6il_rep1a : e6TwoRestQV := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def e6il_rep1b : e6TwoRestQV := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def e6il_rep2a : e6TwoRestQV := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]

@[expose] def e6il_rep2b : e6TwoRestQV := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]

@[expose] def e6il_invMatFn (k : Fin 14) : Fin 16 → Fin 16 → ZMod 2 := fun i j => invMat k i j

@[expose] def e6il_tabW1 : List (List (List (Fin 14))) :=
[
  [[], [], [4], [5], [12, 11, 4], [5, 6, 11], [11, 4], [4, 11, 4], [12, 11], [11], [4, 11], [5, 11], [6, 12, 11], [8, 11], [4, 8, 11], [6, 11]],
  [[13, 10, 4], [5, 6, 10], [10, 4], [4, 10, 4], [2, 12, 11, 4], [2, 5, 6, 11], [2, 11, 4], [2, 4, 11, 4], [], [12], [13], [4, 13], [3], [3, 12], [3, 13], [6, 12]],
  [[13, 10], [10], [4, 10], [5, 10], [3, 9], [3, 9, 12], [3, 9, 13], [3, 12, 9], [2, 12, 11], [2, 11], [2, 4, 11], [2, 5, 11], [9], [9, 12], [9, 13], [12, 9]],
  [[6, 13, 10], [8, 10], [4, 8, 10], [6, 10], [3, 2], [3, 2, 12], [3, 2, 13], [3, 5, 12], [2], [2, 12], [2, 13], [5, 12], [2, 6, 12, 11], [2, 8, 11], [2, 4, 8, 11], [2, 6, 11]],
  [[1, 0], [0], [10, 13, 10], [1, 10, 13, 10], [12, 11, 4, 10], [0, 5, 6, 11], [2, 3, 13, 10], [5, 8, 12, 11], [1, 0, 11], [0, 11], [10, 13], [1, 10, 13], [1, 0, 8, 11], [0, 8, 11], [9, 10, 13], [8, 10, 13]],
  [[13, 10, 4, 11], [0, 5, 6, 10], [13, 10], [1, 13, 10], [1, 5, 6, 10, 11], [5, 6, 10, 11], [3, 13, 10], [0, 11, 4, 13], [10], [0, 12], [10, 4, 11], [1, 10, 4, 11], [3, 10], [0, 3, 12], [3, 10, 4, 11], [2, 11, 5, 10]],
  [[1, 0, 10], [0, 10], [9, 13, 10], [11, 12, 9], [3, 9, 10], [11, 9, 12], [11, 4, 10], [1, 11, 4, 10], [1, 10, 11], [10, 11], [2, 10, 13], [10, 4, 13], [9, 10], [0, 9, 12], [1, 11, 5, 10], [11, 5, 10]],
  [[1, 0, 8, 10], [0, 8, 10], [12, 13, 10], [7, 13, 10], [3, 2, 10], [3, 10, 12], [2, 11, 4, 10], [3, 10, 5, 11], [2, 10], [10, 12], [1, 10, 5, 11], [10, 5, 11], [1, 8, 10, 11], [8, 10, 11], [0, 10, 9, 13], [12, 3, 10]],
  [[1, 0, 4], [11, 12, 11], [0, 4], [1, 11, 12, 11], [1, 0, 11, 4], [2, 3, 11, 12], [0, 11, 4], [2, 11, 4, 13], [1, 0, 4, 11], [12, 11], [0, 4, 11], [1, 12, 11], [1, 0, 4, 8, 11], [9, 12, 11], [0, 4, 8, 11], [6, 12, 11]],
  [[1, 0, 10, 4], [11, 12], [0, 10, 4], [1, 11, 12], [1, 10, 11, 4], [3, 11, 12], [10, 11, 4], [11, 4, 13], [11], [7, 11, 8, 10], [0, 13], [4, 10, 4, 11], [3, 11], [10, 8, 10, 11], [11, 13], [10, 11, 5, 10]],
  [[1, 0, 4, 10], [9, 11, 12], [0, 4, 10], [0, 11, 12, 9], [3, 9, 11], [7, 10, 8, 11], [9, 11, 13], [4, 11, 4, 10], [1, 4, 10, 11], [2, 12, 11], [4, 10, 11], [0, 10, 4, 13], [9, 11], [0, 10, 8, 11], [0, 9, 13], [0, 11, 5, 10]],
  [[1, 0, 4, 8, 10], [10, 11, 12], [0, 4, 8, 10], [5, 11, 12], [3, 2, 11], [11, 8, 10, 11], [5, 11, 13], [10, 4, 11, 4], [2, 11], [0, 11, 8, 10], [0, 2, 13], [0, 10, 5, 11], [1, 4, 8, 10, 11], [0, 10, 3, 12], [4, 8, 10, 11], [12, 9, 11]],
  [[1, 0, 5], [0, 11, 12, 11], [0, 10, 13, 10], [0, 5], [1, 0, 4, 11, 4], [5, 8, 10, 13], [2, 11, 13, 10], [0, 4, 11, 4], [1, 0, 5, 11], [0, 12, 11], [0, 10, 13], [0, 5, 11], [1, 0, 6, 11], [8, 12, 11], [6, 10, 13], [0, 6, 11]],
  [[1, 0, 4, 10, 4], [0, 11, 12], [0, 13, 10], [0, 4, 10, 4], [1, 4, 10, 11, 4], [0, 3, 11, 12], [11, 13, 10], [4, 10, 11, 4], [4, 11], [2, 11, 8, 10], [0, 10, 4, 11], [0, 4, 13], [6, 10], [2, 10, 8, 11], [6, 10, 4, 11], [0, 6, 12]],
  [[1, 0, 5, 10], [13, 10, 9], [0, 9, 13, 10], [0, 5, 10], [3, 10, 9], [3, 10, 8, 11], [0, 11, 4, 10], [0, 3, 12, 9], [1, 5, 10, 11], [10, 12, 11], [0, 2, 10, 13], [5, 10, 11], [10, 9], [10, 8, 11], [1, 10, 8, 11], [0, 12, 9]],
  [[1, 0, 6, 10], [7, 11, 12], [5, 13, 10], [0, 6, 10], [3, 5, 10], [3, 11, 8, 10], [6, 11, 4, 10], [7, 11, 13], [5, 10], [11, 8, 10], [1, 11, 8, 10], [0, 5, 12], [1, 6, 10, 11], [10, 3, 12], [10, 9, 13], [6, 10, 11]]]
@[expose] def e6il_tabF1 : List (List Bool) :=
[
  [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true],
  [false, false, false, false, true, true, true, true, false, false, false, false, true, true, true, true],
  [false, false, false, false, true, true, true, true, true, true, true, true, false, false, false, false],
  [false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true],
  [false, false, true, true, false, false, true, true, true, true, false, false, true, true, false, false],
  [false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, false],
  [false, false, true, true, true, true, false, false, true, true, false, false, false, false, true, true],
  [false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true],
  [false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false],
  [false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false],
  [false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true],
  [false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false],
  [false, true, true, false, false, true, true, false, true, false, false, true, true, false, false, true],
  [false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true],
  [false, true, true, false, true, false, false, true, true, false, false, true, false, true, true, false]]
@[expose] def e6il_bw1a : Fin 8 → List (Fin 14) := ![[], [0], [4], [10], [11], [0, 4], [4, 10], [4, 11]]
@[expose] def e6il_bc1a : Fin 8 → Fin 8 → ZMod 2 := ![![1, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 1, 0, 0, 1], ![1, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 1, 1, 0, 0, 1, 0], ![1, 0, 0, 1, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 1, 0, 0]]
@[expose] def e6il_bw1b : Fin 8 → List (Fin 14) := ![[], [2], [3], [9], [10], [11], [12], [13]]
@[expose] def e6il_bc1b : Fin 8 → Fin 8 → ZMod 2 := ![![1, 0, 0, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 0, 0, 1], ![1, 0, 1, 0, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0], ![0, 1, 1, 1, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 1, 0, 0]]
@[expose] def e6il_tabW2 : List (List (List (Fin 14))) :=
[
  [[], [], [9], [5], [12, 11, 9], [4, 4, 11], [11, 9], [4, 7, 11], [13, 10, 9], [4, 4, 10], [10, 9], [4, 7, 10], [2, 12, 11, 9], [2, 4, 4, 11], [2, 11, 9], [2, 4, 7, 11]],
  [[12, 11], [11], [9, 11], [5, 11], [4, 12, 11], [4, 11], [4, 9, 11], [7, 11], [], [12], [13], [9, 13], [3], [3, 12], [3, 13], [7, 12]],
  [[13, 10], [10], [9, 10], [5, 10], [3, 4], [3, 4, 12], [3, 4, 13], [3, 12, 4], [4, 13, 10], [4, 10], [4, 9, 10], [7, 10], [3, 2], [3, 2, 12], [3, 2, 13], [3, 5, 12]],
  [[2, 12, 11], [2, 11], [2, 9, 11], [2, 5, 11], [4], [4, 12], [4, 13], [12, 4], [2], [2, 12], [2, 13], [5, 12], [2, 4, 12, 11], [2, 4, 11], [2, 4, 9, 11], [2, 7, 11]],
  [[1, 0], [0], [10, 13, 10], [1, 10, 13, 10], [12, 11, 9, 10], [0, 4, 4, 11], [2, 3, 13, 10], [4, 8, 10, 13], [13, 10, 9, 11], [0, 4, 4, 10], [13, 10], [1, 13, 10], [1, 4, 4, 10, 11], [4, 4, 10, 11], [3, 13, 10], [0, 11, 9, 13]],
  [[1, 0, 11], [0, 11], [10, 13], [1, 10, 13], [1, 0, 4, 11], [0, 4, 11], [4, 10, 13], [8, 10, 13], [10], [0, 12], [10, 9, 11], [1, 10, 9, 11], [3, 10], [0, 3, 12], [3, 10, 9, 11], [2, 11, 5, 10]],
  [[1, 0, 10], [0, 10], [4, 13, 10], [11, 12, 4], [3, 4, 10], [11, 4, 12], [11, 9, 10], [1, 11, 9, 10], [1, 0, 4, 10], [0, 4, 10], [12, 13, 10], [6, 13, 10], [3, 2, 10], [3, 10, 12], [2, 11, 9, 10], [3, 10, 5, 11]],
  [[1, 10, 11], [10, 11], [2, 10, 13], [10, 9, 13], [4, 10], [0, 4, 12], [1, 11, 5, 10], [11, 5, 10], [2, 10], [10, 12], [1, 10, 5, 11], [10, 5, 11], [1, 4, 10, 11], [4, 10, 11], [0, 10, 4, 13], [12, 3, 10]],
  [[1, 0, 9], [11, 12, 11], [0, 9], [1, 11, 12, 11], [1, 0, 11, 9], [2, 3, 11, 12], [0, 11, 9], [2, 11, 9, 13], [1, 0, 10, 9], [11, 12], [0, 10, 9], [1, 11, 12], [1, 10, 11, 9], [3, 11, 12], [10, 11, 9], [11, 9, 13]],
  [[1, 0, 9, 11], [12, 11], [0, 9, 11], [1, 12, 11], [1, 0, 4, 9, 11], [4, 12, 11], [0, 4, 9, 11], [7, 12, 11], [11], [6, 11, 4, 10], [0, 13], [9, 10, 9, 11], [3, 11], [10, 4, 10, 11], [11, 13], [10, 11, 5, 10]],
  [[1, 0, 9, 10], [4, 11, 12], [0, 9, 10], [0, 11, 12, 4], [3, 4, 11], [6, 10, 4, 11], [4, 11, 13], [9, 11, 9, 10], [1, 0, 4, 9, 10], [10, 11, 12], [0, 4, 9, 10], [5, 11, 12], [3, 2, 11], [11, 4, 10, 11], [5, 11, 13], [10, 4, 7, 11]],
  [[1, 9, 10, 11], [2, 12, 11], [9, 10, 11], [0, 10, 9, 13], [4, 11], [0, 10, 4, 11], [0, 4, 13], [0, 11, 5, 10], [2, 11], [0, 11, 4, 10], [0, 2, 13], [0, 10, 5, 11], [1, 4, 9, 10, 11], [0, 10, 3, 12], [4, 9, 10, 11], [12, 4, 11]],
  [[1, 0, 5], [0, 11, 12, 11], [0, 10, 13, 10], [0, 5], [1, 0, 4, 7, 11], [4, 8, 12, 11], [2, 11, 13, 10], [0, 4, 7, 11], [1, 0, 4, 7, 10], [0, 11, 12], [0, 13, 10], [0, 4, 7, 10], [1, 4, 7, 10, 11], [0, 3, 11, 12], [11, 13, 10], [4, 7, 10, 11]],
  [[1, 0, 5, 11], [0, 12, 11], [0, 10, 13], [0, 5, 11], [1, 0, 7, 11], [8, 12, 11], [7, 10, 13], [0, 7, 11], [9, 11], [2, 11, 4, 10], [0, 10, 9, 11], [0, 9, 13], [7, 10], [2, 10, 4, 11], [7, 10, 9, 11], [0, 7, 12]],
  [[1, 0, 5, 10], [13, 10, 4], [0, 4, 13, 10], [0, 5, 10], [3, 10, 4], [3, 10, 4, 11], [0, 11, 9, 10], [0, 3, 12, 4], [1, 0, 7, 10], [6, 11, 12], [5, 13, 10], [0, 7, 10], [3, 5, 10], [3, 11, 4, 10], [7, 11, 9, 10], [6, 11, 13]],
  [[1, 5, 10, 11], [10, 12, 11], [0, 2, 10, 13], [5, 10, 11], [10, 4], [10, 4, 11], [1, 10, 4, 11], [0, 12, 4], [5, 10], [11, 4, 10], [1, 11, 4, 10], [0, 5, 12], [1, 7, 10, 11], [10, 3, 12], [10, 4, 13], [7, 10, 11]]]
@[expose] def e6il_tabF2 : List (List Bool) :=
[
  [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true],
  [false, false, false, false, true, true, true, true, false, false, false, false, true, true, true, true],
  [false, false, false, false, true, true, true, true, true, true, true, true, false, false, false, false],
  [false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true],
  [false, false, true, true, false, false, true, true, true, true, false, false, true, true, false, false],
  [false, false, true, true, true, true, false, false, false, false, true, true, true, true, false, false],
  [false, false, true, true, true, true, false, false, true, true, false, false, false, false, true, true],
  [false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true],
  [false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false],
  [false, true, false, true, true, false, true, false, false, true, false, true, true, false, true, false],
  [false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true],
  [false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false],
  [false, true, true, false, false, true, true, false, true, false, false, true, true, false, false, true],
  [false, true, true, false, true, false, false, true, false, true, true, false, true, false, false, true],
  [false, true, true, false, true, false, false, true, true, false, false, true, false, true, true, false]]
@[expose] def e6il_bw2a : Fin 8 → List (Fin 14) := ![[], [0], [5], [10], [11], [0, 5], [5, 10], [5, 11]]
@[expose] def e6il_bc2a : Fin 8 → Fin 8 → ZMod 2 := ![![1, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 1, 0, 0, 1], ![1, 0, 1, 1, 0, 0, 1, 0], ![1, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 0, 1, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 1, 0, 0]]
@[expose] def e6il_bw2b : Fin 8 → List (Fin 14) := ![[], [2], [3], [4], [10], [11], [12], [13]]
@[expose] def e6il_bc2b : Fin 8 → Fin 8 → ZMod 2 := ![![1, 0, 0, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 0, 0, 1], ![1, 0, 1, 0, 0, 0, 0, 0], ![0, 1, 1, 1, 0, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 1, 0, 0]]

@[expose] def e6il_moveWord1 (v : e6TwoRestQV) : List (Fin 14) :=
  (e6il_tabW1.getD (e6il_idxNat1 v / 16) []).getD (e6il_idxNat1 v % 16) []

@[expose] def e6il_moveWord2 (v : e6TwoRestQV) : List (Fin 14) :=
  (e6il_tabW2.getD (e6il_idxNat2 v / 16) []).getD (e6il_idxNat2 v % 16) []

@[expose] def e6il_isRep1 (v : e6TwoRestQV) : Bool :=
  (e6il_tabF1.getD (e6il_idxNat1 v / 16) []).getD (e6il_idxNat1 v % 16) false

@[expose] def e6il_isRep2 (v : e6TwoRestQV) : Bool :=
  (e6il_tabF2.getD (e6il_idxNat2 v / 16) []).getD (e6il_idxNat2 v % 16) false

@[expose] def e6il_repOf1 (v : e6TwoRestQV) : e6TwoRestQV := if e6il_isRep1 v then e6il_rep1b else e6il_rep1a

@[expose] def e6il_repOf2 (v : e6TwoRestQV) : e6TwoRestQV := if e6il_isRep2 v then e6il_rep2b else e6il_rep2a

theorem e6il_vb_reconstruct (v : e6TwoRestQV) (hv : ∀ i : Fin 16, 8 ≤ (i : ℕ) → v i = 0) :
    e6il_vb (e6il_bit v 0) (e6il_bit v 1) (e6il_bit v 2) (e6il_bit v 3)
      (e6il_bit v 4) (e6il_bit v 5) (e6il_bit v 6) (e6il_bit v 7) = v := by
  funext i
  fin_cases i <;> first | exact e6il_zmod2_bit _ | simp [e6il_vb, e6il_bit, e6il_incl, hv]

theorem e6il_wb_reconstruct (v : e6TwoRestQV) (hv : ∀ i : Fin 16, (i : ℕ) < 8 → v i = 0) :
    e6il_wb (e6il_bit2 v 0) (e6il_bit2 v 1) (e6il_bit2 v 2) (e6il_bit2 v 3)
      (e6il_bit2 v 4) (e6il_bit2 v 5) (e6il_bit2 v 6) (e6il_bit2 v 7) = v := by
  funext i
  fin_cases i <;> first | exact e6il_zmod2_bit _ | simp [e6il_wb, e6il_bit2, e6il_incl8, hv]

theorem e6il_move_cert1 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Fin 2,
    e6il_vb b0 b1 b2 b3 b4 b5 b6 b7 ≠ 0 →
    e6il_applyWord (e6il_moveWord1 (e6il_vb b0 b1 b2 b3 b4 b5 b6 b7))
      (e6il_vb b0 b1 b2 b3 b4 b5 b6 b7) =
      e6il_repOf1 (e6il_vb b0 b1 b2 b3 b4 b5 b6 b7) := by
  have hM : ∀ (k : Fin 14) (i j : Fin 16),
      e6il_invMatFn k i j = ILK.dec (ILK.colK k.val j.val) i := by
    decide +kernel
  have hap := ILK.applyWord_dec invMat (fun k i j => hM k i j) e6il_applyWord (fun _ => rfl)
    (fun _ _ _ => rfl)
  have hcase : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Fin 2,
      e6il_vb b0 b1 b2 b3 b4 b5 b6 b7 = ILK.dec (ILK.code8 b0 b1 b2 b3 b4 b5 b6 b7) ∧
      e6il_idxNat1 (e6il_vb b0 b1 b2 b3 b4 b5 b6 b7) = ILK.code8 b0 b1 b2 b3 b4 b5 b6 b7 ∧
      ILK.code8 b0 b1 b2 b3 b4 b5 b6 b7 < 256 := by
    decide +kernel
  have hchk : (List.range 256).all (fun c => c == 0 ||
      ILK.applyK ((e6il_tabW1.getD (c / 16) []).getD (c % 16) []) c ==
        (if (e6il_tabF1.getD (c / 16) []).getD (c % 16) false then 24 else 1)) = true := by
    decide +kernel
  have hra : e6il_rep1a = ILK.dec 1 := by decide +kernel
  have hrb : e6il_rep1b = ILK.dec 24 := by decide +kernel
  intro b0 b1 b2 b3 b4 b5 b6 b7 hne
  obtain ⟨hv, hidx, hlt⟩ := hcase b0 b1 b2 b3 b4 b5 b6 b7
  have hm : e6il_moveWord1 (e6il_vb b0 b1 b2 b3 b4 b5 b6 b7) =
      (e6il_tabW1.getD (ILK.code8 b0 b1 b2 b3 b4 b5 b6 b7 / 16) []).getD
        (ILK.code8 b0 b1 b2 b3 b4 b5 b6 b7 % 16) [] := by
    unfold e6il_moveWord1
    rw [hidx]
  have hr : e6il_repOf1 (e6il_vb b0 b1 b2 b3 b4 b5 b6 b7) = ILK.dec
      (if (e6il_tabF1.getD (ILK.code8 b0 b1 b2 b3 b4 b5 b6 b7 / 16) []).getD
        (ILK.code8 b0 b1 b2 b3 b4 b5 b6 b7 % 16) false then 24 else 1) := by
    unfold e6il_repOf1 e6il_isRep1
    rw [hidx]
    cases (e6il_tabF1.getD (ILK.code8 b0 b1 b2 b3 b4 b5 b6 b7 / 16) []).getD
      (ILK.code8 b0 b1 b2 b3 b4 b5 b6 b7 % 16) false
    · exact hra
    · exact hrb
  rw [hm, hr, hv, hap]
  generalize ILK.code8 b0 b1 b2 b3 b4 b5 b6 b7 = c at hv hlt ⊢
  have hne' : c ≠ 0 := by
    rintro rfl
    exact hne (hv.trans ILK.dec_zero)
  have hk := List.all_eq_true.1 hchk c (List.mem_range.2 hlt)
  simp only [Bool.or_eq_true, beq_iff_eq] at hk
  rcases hk with h | h
  · exact absurd h hne'
  · rw [h]

theorem e6il_move_cert2 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Fin 2,
    e6il_wb b0 b1 b2 b3 b4 b5 b6 b7 ≠ 0 →
    e6il_applyWord (e6il_moveWord2 (e6il_wb b0 b1 b2 b3 b4 b5 b6 b7))
      (e6il_wb b0 b1 b2 b3 b4 b5 b6 b7) =
      e6il_repOf2 (e6il_wb b0 b1 b2 b3 b4 b5 b6 b7) := by
  have hM : ∀ (k : Fin 14) (i j : Fin 16),
      e6il_invMatFn k i j = ILK.dec (ILK.colK k.val j.val) i := by
    decide +kernel
  have hap := ILK.applyWord_dec invMat (fun k i j => hM k i j) e6il_applyWord (fun _ => rfl)
    (fun _ _ _ => rfl)
  have hcase : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Fin 2,
      e6il_wb b0 b1 b2 b3 b4 b5 b6 b7 = ILK.dec (ILK.code8 b0 b1 b2 b3 b4 b5 b6 b7 * 256) ∧
      e6il_idxNat2 (e6il_wb b0 b1 b2 b3 b4 b5 b6 b7) = ILK.code8 b0 b1 b2 b3 b4 b5 b6 b7 ∧
      ILK.code8 b0 b1 b2 b3 b4 b5 b6 b7 < 256 := by
    decide +kernel
  have hchk : (List.range 256).all (fun c => c == 0 ||
      ILK.applyK ((e6il_tabW2.getD (c / 16) []).getD (c % 16) []) (c * 256) ==
        (if (e6il_tabF2.getD (c / 16) []).getD (c % 16) false then 6144 else 256)) = true := by
    decide +kernel
  have hra : e6il_rep2a = ILK.dec 256 := by decide +kernel
  have hrb : e6il_rep2b = ILK.dec 6144 := by decide +kernel
  intro b0 b1 b2 b3 b4 b5 b6 b7 hne
  obtain ⟨hv, hidx, hlt⟩ := hcase b0 b1 b2 b3 b4 b5 b6 b7
  have hm : e6il_moveWord2 (e6il_wb b0 b1 b2 b3 b4 b5 b6 b7) =
      (e6il_tabW2.getD (ILK.code8 b0 b1 b2 b3 b4 b5 b6 b7 / 16) []).getD
        (ILK.code8 b0 b1 b2 b3 b4 b5 b6 b7 % 16) [] := by
    unfold e6il_moveWord2
    rw [hidx]
  have hr : e6il_repOf2 (e6il_wb b0 b1 b2 b3 b4 b5 b6 b7) = ILK.dec
      (if (e6il_tabF2.getD (ILK.code8 b0 b1 b2 b3 b4 b5 b6 b7 / 16) []).getD
        (ILK.code8 b0 b1 b2 b3 b4 b5 b6 b7 % 16) false then 6144 else 256) := by
    unfold e6il_repOf2 e6il_isRep2
    rw [hidx]
    cases (e6il_tabF2.getD (ILK.code8 b0 b1 b2 b3 b4 b5 b6 b7 / 16) []).getD
      (ILK.code8 b0 b1 b2 b3 b4 b5 b6 b7 % 16) false
    · exact hra
    · exact hrb
  rw [hm, hr, hv, hap]
  generalize ILK.code8 b0 b1 b2 b3 b4 b5 b6 b7 = c at hv hlt ⊢
  have hne' : c ≠ 0 := by
    rintro rfl
    rw [Nat.zero_mul, ILK.dec_zero] at hv
    exact hne hv
  have hk := List.all_eq_true.1 hchk c (List.mem_range.2 hlt)
  simp only [Bool.or_eq_true, beq_iff_eq] at hk
  rcases hk with h | h
  · exact absurd h hne'
  · rw [h]

theorem e6il_basis_cert1a : ∀ k : Fin 8,
    e6il_e k = ∑ j : Fin 8, (e6il_bc1a k j) • e6il_applyWord (e6il_bw1a j) e6il_rep1a := by
  decide +kernel

theorem e6il_basis_cert1b : ∀ k : Fin 8,
    e6il_e k = ∑ j : Fin 8, (e6il_bc1b k j) • e6il_applyWord (e6il_bw1b j) e6il_rep1b := by
  decide +kernel

theorem e6il_basis_cert2a : ∀ k : Fin 8,
    e6il_f k = ∑ j : Fin 8, (e6il_bc2a k j) • e6il_applyWord (e6il_bw2a j) e6il_rep2a := by
  decide +kernel

theorem e6il_basis_cert2b : ∀ k : Fin 8,
    e6il_f k = ∑ j : Fin 8, (e6il_bc2b k j) • e6il_applyWord (e6il_bw2b j) e6il_rep2b := by
  decide +kernel

theorem e6il_U1_le_of_basis {W : Submodule (ZMod 2) e6TwoRestQV}
    (hb : ∀ k : Fin 8, e6il_e k ∈ W) : invU1 ≤ W := by
  intro u hu
  rw [← Finset.univ_sum_single u]
  refine Submodule.sum_mem W (fun i _ => ?_)
  by_cases hi : (i : ℕ) < 8
  · have hsingle : (Pi.single i (u i) : e6TwoRestQV) = u i • e6il_e ⟨i, hi⟩ := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [e6il_e, e6il_incl, Pi.single_eq_same]
      · simp [e6il_e, e6il_incl, Pi.single_apply, Pi.smul_apply, hj]
    rw [hsingle]
    exact Submodule.smul_mem W (u i) (hb ⟨i, hi⟩)
  · have hui : u i = 0 := hu i (by omega)
    have hz : (Pi.single i (u i) : e6TwoRestQV) = 0 := by
      rw [hui]; funext j; simp [Pi.single_apply]
    rw [hz]
    exact W.zero_mem

theorem e6il_U2_le_of_basis {W : Submodule (ZMod 2) e6TwoRestQV}
    (hb : ∀ k : Fin 8, e6il_f k ∈ W) : invU2 ≤ W := by
  intro u hu
  rw [← Finset.univ_sum_single u]
  refine Submodule.sum_mem W (fun i _ => ?_)
  by_cases hi : (i : ℕ) < 8
  · have hui : u i = 0 := hu i hi
    have hz : (Pi.single i (u i) : e6TwoRestQV) = 0 := by
      rw [hui]; funext j; simp [Pi.single_apply]
    rw [hz]
    exact W.zero_mem
  · have h8 : 8 ≤ (i : ℕ) := by omega
    have hsingle : (Pi.single i (u i) : e6TwoRestQV) = u i • e6il_f ⟨(i : ℕ) - 8, by omega⟩ := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [e6il_f, e6il_incl8, Pi.single_eq_same, Nat.sub_add_cancel h8]
      · simp [e6il_f, e6il_incl8, Pi.single_apply, Pi.smul_apply, hj, Nat.sub_add_cancel h8]
    rw [hsingle]
    exact Submodule.smul_mem W (u i) (hb ⟨(i : ℕ) - 8, by omega⟩)

theorem e6il_simple_U1 (W : Submodule (ZMod 2) e6TwoRestQV)
    (hW : ∀ k : Fin 14, ∀ v ∈ W, (invMat k).mulVec v ∈ W)
    {v : e6TwoRestQV} (hv : v ∈ invU1) (hv0 : v ≠ 0) (hvW : v ∈ W) : invU1 ≤ W := by
  have hmove := e6il_move_cert1 (e6il_bit v 0) (e6il_bit v 1) (e6il_bit v 2) (e6il_bit v 3)
    (e6il_bit v 4) (e6il_bit v 5) (e6il_bit v 6) (e6il_bit v 7)
  rw [e6il_vb_reconstruct v hv] at hmove
  have hmovev : e6il_applyWord (e6il_moveWord1 v) v = e6il_repOf1 v := hmove hv0
  have hmem : e6il_repOf1 v ∈ W := by
    have h := e6il_applyWord_mem hW (e6il_moveWord1 v) v hvW
    rwa [hmovev] at h
  by_cases hflag : e6il_isRep1 v = true
  · have hb : e6il_rep1b ∈ W := by
      change (if e6il_isRep1 v then e6il_rep1b else e6il_rep1a) ∈ W at hmem
      rwa [if_pos hflag] at hmem
    exact e6il_U1_le_of_basis (fun k => by
      rw [e6il_basis_cert1b k]
      exact Submodule.sum_mem W
        (fun j _ => Submodule.smul_mem W _ (e6il_applyWord_mem hW _ _ hb)))
  · have hb : e6il_rep1a ∈ W := by
      change (if e6il_isRep1 v then e6il_rep1b else e6il_rep1a) ∈ W at hmem
      rw [if_neg hflag] at hmem
      exact hmem
    exact e6il_U1_le_of_basis (fun k => by
      rw [e6il_basis_cert1a k]
      exact Submodule.sum_mem W
        (fun j _ => Submodule.smul_mem W _ (e6il_applyWord_mem hW _ _ hb)))

theorem e6il_simple_U2 (W : Submodule (ZMod 2) e6TwoRestQV)
    (hW : ∀ k : Fin 14, ∀ v ∈ W, (invMat k).mulVec v ∈ W)
    {v : e6TwoRestQV} (hv : v ∈ invU2) (hv0 : v ≠ 0) (hvW : v ∈ W) : invU2 ≤ W := by
  have hmove := e6il_move_cert2 (e6il_bit2 v 0) (e6il_bit2 v 1) (e6il_bit2 v 2) (e6il_bit2 v 3)
    (e6il_bit2 v 4) (e6il_bit2 v 5) (e6il_bit2 v 6) (e6il_bit2 v 7)
  rw [e6il_wb_reconstruct v hv] at hmove
  have hmovev : e6il_applyWord (e6il_moveWord2 v) v = e6il_repOf2 v := hmove hv0
  have hmem : e6il_repOf2 v ∈ W := by
    have h := e6il_applyWord_mem hW (e6il_moveWord2 v) v hvW
    rwa [hmovev] at h
  by_cases hflag : e6il_isRep2 v = true
  · have hb : e6il_rep2b ∈ W := by
      change (if e6il_isRep2 v then e6il_rep2b else e6il_rep2a) ∈ W at hmem
      rwa [if_pos hflag] at hmem
    exact e6il_U2_le_of_basis (fun k => by
      rw [e6il_basis_cert2b k]
      exact Submodule.sum_mem W
        (fun j _ => Submodule.smul_mem W _ (e6il_applyWord_mem hW _ _ hb)))
  · have hb : e6il_rep2a ∈ W := by
      change (if e6il_isRep2 v then e6il_rep2b else e6il_rep2a) ∈ W at hmem
      rw [if_neg hflag] at hmem
      exact hmem
    exact e6il_U2_le_of_basis (fun k => by
      rw [e6il_basis_cert2a k]
      exact Submodule.sum_mem W
        (fun j _ => Submodule.smul_mem W _ (e6il_applyWord_mem hW _ _ hb)))

@[expose] def e6il_Y1 : Matrix (Fin 16) (Fin 16) (ZMod 2) :=
  invMat 6 + invMat 1 * invMat 8 * invMat 0

@[expose] def e6il_P1 : Matrix (Fin 16) (Fin 16) (ZMod 2) := e6il_Y1 ^ 2

@[expose] def e6il_Y2 : Matrix (Fin 16) (Fin 16) (ZMod 2) :=
  invMat 1 * invMat 13 * invMat 8 + invMat 4 * invMat 11 * invMat 3
    + invMat 8 * invMat 6 * invMat 0

@[expose] def e6il_P2 : Matrix (Fin 16) (Fin 16) (ZMod 2) := e6il_Y2 ^ 6

@[expose] def e6il_Preserves (W : Submodule (ZMod 2) e6TwoRestQV)
    (M : Matrix (Fin 16) (Fin 16) (ZMod 2)) : Prop := ∀ v ∈ W, M.mulVec v ∈ W

theorem e6il_preserves_add {W : Submodule (ZMod 2) e6TwoRestQV}
    {M N : Matrix (Fin 16) (Fin 16) (ZMod 2)} (hM : e6il_Preserves W M)
    (hN : e6il_Preserves W N) : e6il_Preserves W (M + N) := by
  intro v hv
  rw [Matrix.add_mulVec]
  exact W.add_mem (hM v hv) (hN v hv)

theorem e6il_preserves_mul {W : Submodule (ZMod 2) e6TwoRestQV}
    {M N : Matrix (Fin 16) (Fin 16) (ZMod 2)} (hM : e6il_Preserves W M)
    (hN : e6il_Preserves W N) : e6il_Preserves W (M * N) := by
  intro v hv
  rw [← Matrix.mulVec_mulVec]
  exact hM _ (hN v hv)

theorem e6il_preserves_pow {W : Submodule (ZMod 2) e6TwoRestQV}
    {M : Matrix (Fin 16) (Fin 16) (ZMod 2)} (hM : e6il_Preserves W M) :
    ∀ n : ℕ, e6il_Preserves W (M ^ n) := by
  intro n
  induction n with
  | zero => intro v hv; rw [pow_zero, Matrix.one_mulVec]; exact hv
  | succ n ih => intro v hv; rw [pow_succ, ← Matrix.mulVec_mulVec]; exact ih _ (hM v hv)

theorem e6il_preserves_Y1 {W : Submodule (ZMod 2) e6TwoRestQV}
    (hW : ∀ k : Fin 14, ∀ v ∈ W, (invMat k).mulVec v ∈ W) :
    e6il_Preserves W e6il_Y1 := by
  show e6il_Preserves W (invMat 6 + invMat 1 * invMat 8 * invMat 0)
  exact e6il_preserves_add (hW 6)
    (e6il_preserves_mul (e6il_preserves_mul (hW 1) (hW 8)) (hW 0))

theorem e6il_preserves_P1 {W : Submodule (ZMod 2) e6TwoRestQV}
    (hW : ∀ k : Fin 14, ∀ v ∈ W, (invMat k).mulVec v ∈ W) :
    e6il_Preserves W e6il_P1 := by
  show e6il_Preserves W (e6il_Y1 ^ 2)
  exact e6il_preserves_pow (e6il_preserves_Y1 hW) 2

theorem e6il_preserves_Y2 {W : Submodule (ZMod 2) e6TwoRestQV}
    (hW : ∀ k : Fin 14, ∀ v ∈ W, (invMat k).mulVec v ∈ W) :
    e6il_Preserves W e6il_Y2 := by
  show e6il_Preserves W
    (invMat 1 * invMat 13 * invMat 8 + invMat 4 * invMat 11 * invMat 3
      + invMat 8 * invMat 6 * invMat 0)
  exact e6il_preserves_add
    (e6il_preserves_add
      (e6il_preserves_mul (e6il_preserves_mul (hW 1) (hW 13)) (hW 8))
      (e6il_preserves_mul (e6il_preserves_mul (hW 4) (hW 11)) (hW 3)))
    (e6il_preserves_mul (e6il_preserves_mul (hW 8) (hW 6)) (hW 0))

theorem e6il_preserves_P2 {W : Submodule (ZMod 2) e6TwoRestQV}
    (hW : ∀ k : Fin 14, ∀ v ∈ W, (invMat k).mulVec v ∈ W) :
    e6il_Preserves W e6il_P2 := by
  show e6il_Preserves W (e6il_Y2 ^ 6)
  exact e6il_preserves_pow (e6il_preserves_Y2 hW) 6

@[expose] def e6il_P1lit : Matrix (Fin 16) (Fin 16) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1]

@[expose] def e6il_P2lit : Matrix (Fin 16) (Fin 16) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0;
      1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem e6il_P1_eq : e6il_P1 = e6il_P1lit := by
  have hk : ∀ k : Fin 14, (∀ i j : Fin 16,
      e6il_invMatFn k i j = ILK.dec (ILK.colK k.val j.val) i) →
      invMat k = ILK.matC (ILK.colK k.val) := fun k h => ILK.eq_matC (fun i j => h i j)
  have h6 := hk 6 (by decide +kernel)
  have h1 := hk 1 (by decide +kernel)
  have h8 := hk 8 (by decide +kernel)
  have h0 := hk 0 (by decide +kernel)
  have hY : e6il_Y1 = ILK.matC (ILK.colOf ILK.y1C) := by
    unfold e6il_Y1
    rw [h6, h1, h8, h0, ILK.matC_mul, ILK.matC_mul, ILK.matC_add]
    exact ILK.matC_congr (by decide +kernel)
  have hlit : ∀ i j : Fin 16, e6il_P1lit i j = ILK.dec (ILK.colOf ILK.p1C j.val) i :=
    ILK.eqColB_sound (f := e6il_P1lit) (by decide +kernel)
  have hP : e6il_P1lit = ILK.matC (ILK.colOf ILK.p1C) := ILK.eq_matC hlit
  unfold e6il_P1
  rw [hY, hP, pow_two, ILK.matC_mul]
  exact ILK.matC_congr (by decide +kernel)

theorem e6il_P2_eq : e6il_P2 = e6il_P2lit := by
  have hk : ∀ k : Fin 14, (∀ i j : Fin 16,
      e6il_invMatFn k i j = ILK.dec (ILK.colK k.val j.val) i) →
      invMat k = ILK.matC (ILK.colK k.val) := fun k h => ILK.eq_matC (fun i j => h i j)
  have h0 := hk 0 (by decide +kernel)
  have h1 := hk 1 (by decide +kernel)
  have h3 := hk 3 (by decide +kernel)
  have h4 := hk 4 (by decide +kernel)
  have h6 := hk 6 (by decide +kernel)
  have h8 := hk 8 (by decide +kernel)
  have h11 := hk 11 (by decide +kernel)
  have h13 := hk 13 (by decide +kernel)
  have hY : e6il_Y2 = ILK.matC (ILK.colOf ILK.y2C) := by
    unfold e6il_Y2
    rw [h0, h1, h3, h4, h6, h8, h11, h13, ILK.matC_mul, ILK.matC_mul, ILK.matC_mul,
      ILK.matC_mul, ILK.matC_mul, ILK.matC_mul, ILK.matC_add, ILK.matC_add]
    exact ILK.matC_congr (by decide +kernel)
  have hQ : ILK.matC (ILK.colOf ILK.y2C) * ILK.matC (ILK.colOf ILK.y2C) =
      ILK.matC (ILK.colOf ILK.y2sqC) := by
    rw [ILK.matC_mul]
    exact ILK.matC_congr (by decide +kernel)
  have hlit : ∀ i j : Fin 16, e6il_P2lit i j = ILK.dec (ILK.colOf ILK.p2C j.val) i :=
    ILK.eqColB_sound (f := e6il_P2lit) (by decide +kernel)
  have hP : e6il_P2lit = ILK.matC (ILK.colOf ILK.p2C) := ILK.eq_matC hlit
  have e6 : (6 : ℕ) = 2 * 3 := rfl
  unfold e6il_P2
  rw [e6, pow_mul, pow_two, pow_three', hY, hQ, hP, ILK.matC_mul, ILK.matC_mul]
  exact ILK.matC_congr (by decide +kernel)

theorem e6il_preserves_P1lit {W : Submodule (ZMod 2) e6TwoRestQV}
    (hW : ∀ k : Fin 14, ∀ v ∈ W, (invMat k).mulVec v ∈ W) :
    e6il_Preserves W e6il_P1lit := by
  rw [← e6il_P1_eq]
  exact e6il_preserves_P1 hW

theorem e6il_preserves_P2lit {W : Submodule (ZMod 2) e6TwoRestQV}
    (hW : ∀ k : Fin 14, ∀ v ∈ W, (invMat k).mulVec v ∈ W) :
    e6il_Preserves W e6il_P2lit := by
  rw [← e6il_P2_eq]
  exact e6il_preserves_P2 hW

@[expose] def e6il_P1fn : Fin 16 → Fin 16 → ZMod 2 := fun i j => e6il_P1lit i j

@[expose] def e6il_P2fn : Fin 16 → Fin 16 → ZMod 2 := fun i j => e6il_P2lit i j

theorem e6il_P1_cols : ∀ i j : Fin 16, (j : ℕ) < 8 → e6il_P1fn i j = 0 := by
  decide +kernel

theorem e6il_P1_rows : ∀ i j : Fin 16, (i : ℕ) < 8 → e6il_P1fn i j = 0 := by
  decide +kernel

theorem e6il_P2_cols : ∀ i j : Fin 16, 8 ≤ (j : ℕ) → e6il_P2fn i j = 0 := by
  decide +kernel

theorem e6il_P2_rows : ∀ i j : Fin 16, 8 ≤ (i : ℕ) → e6il_P2fn i j = 0 := by
  decide +kernel

theorem e6il_P1_kill_U1 {v : e6TwoRestQV} (hv : v ∈ invU1) : e6il_P1lit.mulVec v = 0 := by
  funext i
  simp only [Matrix.mulVec_apply, Matrix.row, dotProduct]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : (j : ℕ) < 8
  · rw [show e6il_P1lit i j = 0 from e6il_P1_cols i j hj, zero_mul]
  · rw [hv j (by omega), mul_zero]

theorem e6il_P1_maps_U2 (v : e6TwoRestQV) : e6il_P1lit.mulVec v ∈ invU2 := by
  intro i hi
  simp only [Matrix.mulVec_apply, Matrix.row, dotProduct]
  apply Finset.sum_eq_zero
  intro j _
  rw [show e6il_P1lit i j = 0 from e6il_P1_rows i j hi, zero_mul]

theorem e6il_P2_kill_U2 {v : e6TwoRestQV} (hv : v ∈ invU2) : e6il_P2lit.mulVec v = 0 := by
  funext i
  simp only [Matrix.mulVec_apply, Matrix.row, dotProduct]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : (j : ℕ) < 8
  · rw [hv j hj, mul_zero]
  · rw [show e6il_P2lit i j = 0 from e6il_P2_cols i j (by omega), zero_mul]

theorem e6il_P2_maps_U1 (v : e6TwoRestQV) : e6il_P2lit.mulVec v ∈ invU1 := by
  intro i hi
  simp only [Matrix.mulVec_apply, Matrix.row, dotProduct]
  apply Finset.sum_eq_zero
  intro j _
  rw [show e6il_P2lit i j = 0 from e6il_P2_rows i j hi, zero_mul]

theorem e6il_P1_inj_U2 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Fin 2,
    e6il_wb b0 b1 b2 b3 b4 b5 b6 b7 ≠ 0 →
    e6il_P1lit.mulVec (e6il_wb b0 b1 b2 b3 b4 b5 b6 b7) ≠ 0 := by
  have hlit : ∀ i j : Fin 16, e6il_P1lit i j = ILK.dec (ILK.colOf ILK.p1C j.val) i :=
    ILK.eqColB_sound (f := e6il_P1lit) (by decide +kernel)
  have hcase : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Fin 2,
      e6il_wb b0 b1 b2 b3 b4 b5 b6 b7 = ILK.dec (ILK.code8 b0 b1 b2 b3 b4 b5 b6 b7 * 256) ∧
      ILK.code8 b0 b1 b2 b3 b4 b5 b6 b7 < 256 := by
    decide +kernel
  have hchk : (List.range 256).all (fun c => c == 0 ||
      Nat.blt 0 (ILK.mulCm (ILK.colOf ILK.p1C) (c * 256) 16 % 65536)) = true := by
    decide +kernel
  intro b0 b1 b2 b3 b4 b5 b6 b7 hne
  obtain ⟨hv, hlt⟩ := hcase b0 b1 b2 b3 b4 b5 b6 b7
  rw [hv] at hne ⊢
  rw [ILK.mulVec_dec e6il_P1lit (ILK.colOf ILK.p1C) hlit]
  apply ILK.dec_ne_zero
  generalize ILK.code8 b0 b1 b2 b3 b4 b5 b6 b7 = c at hne hlt ⊢
  have hne' : c ≠ 0 := by
    rintro rfl
    rw [Nat.zero_mul, ILK.dec_zero] at hne
    exact hne rfl
  have hk := List.all_eq_true.1 hchk c (List.mem_range.2 hlt)
  simp only [Bool.or_eq_true, beq_iff_eq, Nat.blt_eq] at hk
  rcases hk with h | h
  · exact absurd h hne'
  · exact Nat.pos_iff_ne_zero.1 h

theorem e6il_P2_inj_U1 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Fin 2,
    e6il_vb b0 b1 b2 b3 b4 b5 b6 b7 ≠ 0 →
    e6il_P2lit.mulVec (e6il_vb b0 b1 b2 b3 b4 b5 b6 b7) ≠ 0 := by
  decide +kernel

theorem e6il_P1_inj_U2' {v : e6TwoRestQV} (hv : v ∈ invU2) (hv0 : v ≠ 0) :
    e6il_P1lit.mulVec v ≠ 0 := by
  have hmove := e6il_P1_inj_U2 (e6il_bit2 v 0) (e6il_bit2 v 1) (e6il_bit2 v 2)
    (e6il_bit2 v 3) (e6il_bit2 v 4) (e6il_bit2 v 5) (e6il_bit2 v 6) (e6il_bit2 v 7)
  rw [e6il_wb_reconstruct v hv] at hmove
  exact hmove hv0

theorem e6il_P2_inj_U1' {v : e6TwoRestQV} (hv : v ∈ invU1) (hv0 : v ≠ 0) :
    e6il_P2lit.mulVec v ≠ 0 := by
  have hmove := e6il_P2_inj_U1 (e6il_bit v 0) (e6il_bit v 1) (e6il_bit v 2)
    (e6il_bit v 3) (e6il_bit v 4) (e6il_bit v 5) (e6il_bit v 6) (e6il_bit v 7)
  rw [e6il_vb_reconstruct v hv] at hmove
  exact hmove hv0

@[expose] def e6il_proj1 (v : e6TwoRestQV) : e6TwoRestQV := fun i => if (i : ℕ) < 8 then v i else 0

@[expose] def e6il_proj2 (v : e6TwoRestQV) : e6TwoRestQV := fun i => if (i : ℕ) < 8 then 0 else v i

theorem e6il_proj1_mem (v : e6TwoRestQV) : e6il_proj1 v ∈ invU1 := by
  intro i hi
  simp only [e6il_proj1]
  exact if_neg (by omega)

theorem e6il_proj2_mem (v : e6TwoRestQV) : e6il_proj2 v ∈ invU2 := by
  intro i hi
  simp only [e6il_proj2]
  exact if_pos hi

theorem e6il_proj1_add_proj2 (v : e6TwoRestQV) : e6il_proj1 v + e6il_proj2 v = v := by
  funext i
  by_cases hi : (i : ℕ) < 8 <;> simp [e6il_proj1, e6il_proj2, hi]

theorem invariant_submodule_classification (W : Submodule (ZMod 2) e6TwoRestQV)
    (hW : ∀ k : Fin 14, ∀ v ∈ W, (invMat k).mulVec v ∈ W) :
    W = ⊥ ∨ W = invU1 ∨ W = invU2 ∨ W = ⊤ := by
  have hP1 : e6il_Preserves W e6il_P1lit := e6il_preserves_P1lit hW
  have hP2 : e6il_Preserves W e6il_P2lit := e6il_preserves_P2lit hW
  have hA_imp : (∃ w ∈ W, e6il_proj1 w ≠ 0) → invU1 ≤ W := by
    rintro ⟨w, hwW, hw1⟩
    have hP2w : e6il_P2lit.mulVec w ∈ W := hP2 w hwW
    have hkill2 : e6il_P2lit.mulVec (e6il_proj2 w) = 0 :=
      e6il_P2_kill_U2 (e6il_proj2_mem w)
    have hsplit : e6il_P2lit.mulVec w = e6il_P2lit.mulVec (e6il_proj1 w) := by
      conv_lhs => rw [(e6il_proj1_add_proj2 w).symm]
      rw [Matrix.mulVec_add, hkill2, add_zero]
    have hmem1 : e6il_P2lit.mulVec (e6il_proj1 w) ∈ W := by
      rw [← hsplit]; exact hP2w
    exact e6il_simple_U1 W hW (e6il_P2_maps_U1 (e6il_proj1 w))
      (e6il_P2_inj_U1' (e6il_proj1_mem w) hw1) hmem1
  have hB_imp : (∃ w ∈ W, e6il_proj2 w ≠ 0) → invU2 ≤ W := by
    rintro ⟨w, hwW, hw2⟩
    have hP1w : e6il_P1lit.mulVec w ∈ W := hP1 w hwW
    have hkill1 : e6il_P1lit.mulVec (e6il_proj1 w) = 0 :=
      e6il_P1_kill_U1 (e6il_proj1_mem w)
    have hsplit : e6il_P1lit.mulVec w = e6il_P1lit.mulVec (e6il_proj2 w) := by
      conv_lhs => rw [(e6il_proj1_add_proj2 w).symm]
      rw [Matrix.mulVec_add, hkill1, zero_add]
    have hmem2 : e6il_P1lit.mulVec (e6il_proj2 w) ∈ W := by
      rw [← hsplit]; exact hP1w
    exact e6il_simple_U2 W hW (e6il_P1_maps_U2 (e6il_proj2 w))
      (e6il_P1_inj_U2' (e6il_proj2_mem w) hw2) hmem2
  by_cases hA : ∃ w ∈ W, e6il_proj1 w ≠ 0
  · have hU1 : invU1 ≤ W := hA_imp hA
    by_cases hB : ∃ w ∈ W, e6il_proj2 w ≠ 0
    · have hU2 : invU2 ≤ W := hB_imp hB
      refine Or.inr (Or.inr (Or.inr ?_))
      refine le_antisymm le_top ?_
      intro v _
      rw [← e6il_proj1_add_proj2 v]
      exact W.add_mem (hU1 (e6il_proj1_mem v)) (hU2 (e6il_proj2_mem v))
    · refine Or.inr (Or.inl ?_)
      refine le_antisymm ?_ hU1
      intro w hw
      have h2 : e6il_proj2 w = 0 := by
        by_contra hne; exact hB ⟨w, hw, hne⟩
      have hw' : w = e6il_proj1 w + e6il_proj2 w := (e6il_proj1_add_proj2 w).symm
      rw [hw', h2, add_zero]
      exact e6il_proj1_mem w
  · by_cases hB : ∃ w ∈ W, e6il_proj2 w ≠ 0
    · have hU2 : invU2 ≤ W := hB_imp hB
      refine Or.inr (Or.inr (Or.inl ?_))
      refine le_antisymm ?_ hU2
      intro w hw
      have h1 : e6il_proj1 w = 0 := by
        by_contra hne; exact hA ⟨w, hw, hne⟩
      have hw' : w = e6il_proj1 w + e6il_proj2 w := (e6il_proj1_add_proj2 w).symm
      rw [hw', h1, zero_add]
      exact e6il_proj2_mem w
    · refine Or.inl ?_
      rw [Submodule.eq_bot_iff]
      intro w hw
      have h1 : e6il_proj1 w = 0 := by
        by_contra hne; exact hA ⟨w, hw, hne⟩
      have h2 : e6il_proj2 w = 0 := by
        by_contra hne; exact hB ⟨w, hw, hne⟩
      have hw' : w = e6il_proj1 w + e6il_proj2 w := (e6il_proj1_add_proj2 w).symm
      rw [hw', h1, h2, add_zero]

end CFSG.StandardType.GGSixE6Two
