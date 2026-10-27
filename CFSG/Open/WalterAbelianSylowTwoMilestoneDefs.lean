module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Open

open Matrix
open scoped MatrixGroups

@[expose] def walterJ1GenA : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![0, 7, 9, 9, 10, 7, 9;
     7, 0, 1, 4, 3, 3, 4;
     9, 1, 2, 8, 3, 6, 2;
     9, 4, 8, 10, 1, 6, 0;
     10, 3, 3, 1, 8, 9, 1;
     7, 3, 6, 6, 9, 1, 3;
     9, 4, 2, 0, 1, 3, 0]

@[expose] def walterJ1GenB : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![5, 7, 1, 8, 5, 8, 2;
     10, 4, 10, 0, 3, 3, 8;
     5, 10, 8, 9, 1, 2, 1;
     2, 3, 3, 6, 1, 2, 9;
     7, 4, 7, 2, 10, 7, 3;
     3, 9, 0, 4, 2, 3, 5;
     3, 4, 3, 3, 9, 4, 9]

@[expose] def walterJ1 : Subgroup (GL (Fin 7) (ZMod 11)) :=
  Subgroup.closure {g | (g : Matrix (Fin 7) (Fin 7) (ZMod 11)) = walterJ1GenA ∨
    (g : Matrix (Fin 7) (Fin 7) (ZMod 11)) = walterJ1GenB}

end CFSG.Open
