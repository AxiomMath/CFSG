module

public import CFSG.Quasithin.Background.JonesParshallG2TwoInputs

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix Matrix.SpecialLinearGroup CFSG.Quasithin.Explicit CFSG.Open
open scoped commutatorElement

section Mat

variable {F : Type} [Field F]

@[expose] def zornBlockMat (A C : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 8) (Fin 8) F :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, A 0 0, A 0 1, A 0 2, 0, 0, 0, 0;
    0, A 1 0, A 1 1, A 1 2, 0, 0, 0, 0;
    0, A 2 0, A 2 1, A 2 2, 0, 0, 0, 0;
    0, 0, 0, 0, C 0 0, C 0 1, C 0 2, 0;
    0, 0, 0, 0, C 1 0, C 1 1, C 1 2, 0;
    0, 0, 0, 0, C 2 0, C 2 1, C 2 2, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

end Mat

section Two

@[expose] def matA2 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 1, 0, 1, 1, 1, 1, 0;
    1, 1, 1, 1, 0, 1, 0, 1;
    0, 1, 1, 0, 1, 1, 1, 0;
    1, 0, 1, 0, 0, 1, 0, 1;
    1, 0, 1, 1, 1, 1, 0, 1;
    0, 1, 0, 1, 1, 0, 1, 0;
    1, 0, 1, 1, 0, 0, 1, 1;
    0, 1, 0, 1, 1, 1, 1, 1]

@[expose] def matB2 : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 1, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 1, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 1, 0;
    0, 0, 0, 0, 1, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def mats8 : Fin 8 → Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  ![matX2, matY2, zornBlockMat (Matrix.transvection 0 1 1) (Matrix.transvection 1 0 1),
    zornBlockMat (Matrix.transvection 0 2 1) (Matrix.transvection 2 0 1),
    zornBlockMat (Matrix.transvection 1 0 1) (Matrix.transvection 0 1 1),
    zornBlockMat (Matrix.transvection 1 2 1) (Matrix.transvection 2 1 1),
    zornBlockMat (Matrix.transvection 2 0 1) (Matrix.transvection 0 2 1),
    zornBlockMat (Matrix.transvection 2 1 1) (Matrix.transvection 1 2 1)]

@[expose] def wordsG : Fin 8 → List (Fin 3) :=
  ![[0], [1, 0, 1, 0, 2, 1, 0, 1, 2], [2, 1, 0, 1, 1, 0, 1, 2, 2], [1, 0, 1, 1, 0, 1],
    [2, 1, 0, 1, 2, 1, 1, 2, 1, 0, 1, 2], [0, 2, 1, 1, 2, 1, 1, 0, 2, 1, 2, 1, 2],
    [1, 2, 1, 0, 2, 1, 1, 2, 1, 0, 1], [0, 1, 0, 1, 2, 2, 1, 0, 1, 2, 1, 0, 1]]

end Two

end CFSG.Quasithin.JonesParshall
