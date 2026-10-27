module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gs03Check
public import CFSG.GH74.KGroups.U33Inputs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Gs03U33

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.Sporadic.Schreier

@[expose] def u33Classes :
    List (Equiv.Perm (Fin 28) × List (Equiv.Perm (Fin 28)) × List (List ℕ)) :=
  [(List.formPerm [4, 7] * List.formPerm [5, 8] * List.formPerm [6, 9] *
      List.formPerm [10, 19] * List.formPerm [11, 20] * List.formPerm [12, 21] *
      List.formPerm [13, 25] * List.formPerm [14, 26] * List.formPerm [15, 27] *
      List.formPerm [16, 22] * List.formPerm [17, 23] * List.formPerm [18, 24],
    [1,
     List.formPerm [0, 26, 6, 7, 14, 11, 8, 23, 13, 9, 17, 1] *
       List.formPerm [2, 27, 3, 25, 16, 24, 5, 21, 20, 18, 10, 4] * List.formPerm [12, 22, 19],
     List.formPerm [0, 7, 19, 17, 15, 5, 18, 23, 13, 16, 1, 26] *
       List.formPerm [2, 21, 20, 22, 12, 24, 27, 9, 4, 11, 6, 3] * List.formPerm [8, 10, 25],
     List.formPerm [0, 10, 3, 9, 21, 4, 8, 16, 20, 7, 27, 24] *
       List.formPerm [1, 2, 17, 13, 18, 23, 11, 5, 14, 6, 25, 26] * List.formPerm [12, 15, 22]],
    [[0, 3, 1, 0, 2, 1, 2, 0, 1], [0, 2, 0, 1, 2, 3, 1, 2, 1, 0, 3, 1, 2, 3, 1, 2, 1]]),
   (List.formPerm [2, 3] * List.formPerm [5, 6] * List.formPerm [8, 9] *
      List.formPerm [10, 19] * List.formPerm [11, 21] * List.formPerm [12, 20] *
      List.formPerm [13, 22] * List.formPerm [14, 24] * List.formPerm [15, 23] *
      List.formPerm [16, 25] * List.formPerm [17, 27] * List.formPerm [18, 26],
    [List.formPerm [0, 10, 3, 25, 18, 21, 26, 22, 17, 27, 6, 13] *
       List.formPerm [1, 14, 11, 15, 12, 5, 23, 2, 8, 7, 4, 20] * List.formPerm [9, 19, 24],
     List.formPerm [0, 24, 4, 16, 26, 15, 17, 10, 25, 18, 1, 21] *
       List.formPerm [2, 14, 5, 19, 22, 20, 23, 3, 11, 6, 9, 8] * List.formPerm [7, 13, 12],
     List.formPerm [0, 10, 16, 9, 15, 25, 7, 3, 13, 8, 5, 22] *
       List.formPerm [1, 23, 12, 27, 19, 26, 4, 6, 18, 17, 2, 20] * List.formPerm [11, 21, 24],
     1],
    [[3, 1, 0, 1, 3, 1, 2, 0, 2, 1, 0, 1, 3, 2], [3, 2, 1, 0, 1, 2, 0, 2, 1, 0]])]

@[expose] def u33GenCheck (_ : Unit := ()) : Bool :=
  decide ((u33Classes.map fun c => c.1) = [pu, pt2]) &&
    gs03ClassesCheck QP [pa, pb] 4 u33Classes

end CFSG.LocalAnalysis.WeakClosure81.Gs03U33
