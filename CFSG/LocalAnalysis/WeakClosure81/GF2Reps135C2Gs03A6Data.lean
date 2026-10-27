module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gs03Check
public import CFSG.GH74.KGroups.A6Inputs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Gs03A6

open CFSG.GH74.KGroups CFSG.GH74.KGroups.A6 CFSG.Sporadic.Schreier

@[expose] def a6Classes : List (Equiv.Perm (Fin 10) × List (Equiv.Perm (Fin 10)) × List (List ℕ)) :=
  [(List.formPerm [0, 9] * List.formPerm [1, 2] * List.formPerm [4, 7] * List.formPerm [5, 8],
    [List.formPerm [0, 8] * List.formPerm [1, 7] * List.formPerm [2, 6] * List.formPerm [3, 5],
     List.formPerm [0, 6] * List.formPerm [1, 7] * List.formPerm [3, 4] * List.formPerm [5, 9],
     List.formPerm [0, 7, 4, 2] * List.formPerm [1, 3, 9, 8],
     1,
     1],
    [[3], [1, 2, 1, 3, 1, 3, 1, 0, 1, 0]]),
   (List.formPerm [1, 5] * List.formPerm [2, 4] * List.formPerm [6, 9],
    [List.formPerm [0, 1, 5, 8] * List.formPerm [2, 7, 9, 3],
     List.formPerm [0, 1] * List.formPerm [3, 7] * List.formPerm [4, 6] * List.formPerm [5, 8],
     List.formPerm [0, 6] * List.formPerm [1, 8] * List.formPerm [2, 7] * List.formPerm [4, 5],
     1,
     List.formPerm [1, 3, 2, 6] * List.formPerm [4, 5, 8, 7]],
    [[1, 0, 3, 0, 1, 2, 4, 0, 2, 1, 0, 3, 0, 1, 0, 4], [4, 2, 4, 2, 3, 2, 1, 0]]),
   (List.formPerm [0, 3] * List.formPerm [1, 6] * List.formPerm [2, 7] *
      List.formPerm [4, 9] * List.formPerm [5, 8],
    [List.formPerm [1, 4, 9, 7] * List.formPerm [3, 8, 5, 6],
     List.formPerm [0, 6] * List.formPerm [2, 8] * List.formPerm [3, 5] * List.formPerm [4, 9],
     List.formPerm [0, 2] * List.formPerm [3, 8] * List.formPerm [4, 7] * List.formPerm [5, 6],
     1,
     1],
    [[0, 1, 0, 2, 1, 3], [1, 0, 3, 1, 2, 1, 0, 1, 3, 0]])]

@[expose] def a6GenCheck (_ : Unit := ()) : Bool :=
  gs03CoverCheck (elemsT QA) (a6Classes.map fun c => c.1) &&
    gs03ClassesCheck QP [pa, pb] 5 a6Classes

end CFSG.LocalAnalysis.WeakClosure81.Gs03A6
