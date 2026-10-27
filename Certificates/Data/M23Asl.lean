module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermExtCheck
public import CFSG.Quasithin.Background.HSporLatInputs
public import CFSG.Sporadic.Schreier.M23Gens

public section

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L PermLat
open CFSG.Sporadic.Schreier (m23PermA m23PermB)

namespace M23Asl

@[expose] def tabP (g : Perm (Fin 23)) : Array ℕ :=
  ((List.finRange 23).map fun i => (g i).val).toArray

@[expose] def sgPerms : List (Perm (Fin 23)) :=
  [permOf 23 [[0, 9], [1, 8], [2, 3], [5, 16], [6, 7], [10, 22], [12, 20], [13, 21]],
   permOf 23 [[0, 5, 16, 9], [1, 7, 2, 14, 10, 12, 3, 17], [6, 13, 11, 22, 20, 21, 19, 8],
     [15, 18]],
   permOf 23 [[1, 3], [2, 10], [5, 9], [6, 20], [8, 13], [14, 17], [15, 18], [21, 22]]]

@[expose] def wa : List ℕ := [1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1]

@[expose] def wb : List ℕ := [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0]

@[expose] def yaGens : List (Perm (Fin 23)) := sgPerms ++ [evalW [m23PermA, m23PermB] wa]

@[expose] def ybGens : List (Perm (Fin 23)) := sgPerms ++ [evalW [m23PermA, m23PermB] wb]

@[expose] def aaGens : List (Perm (Fin 23)) :=
  [permOf 23 [[0, 9, 5], [1, 17, 7], [2, 3, 13], [6, 8, 14], [10, 19, 20], [11, 12, 22]],
   permOf 23 [[0, 11, 6, 21, 10], [1, 9, 19, 7, 2], [3, 8, 5, 14, 12], [13, 22, 16, 17, 20]]]

@[expose] def abGens : List (Perm (Fin 23)) :=
  [permOf 23 [[2, 20, 14], [3, 11, 7], [4, 5, 9], [6, 12, 8], [10, 21, 13], [17, 22, 19]],
   permOf 23 [[0, 4, 16, 9, 5], [1, 13, 10, 19, 14], [2, 17, 20, 12, 11], [6, 22, 8, 7, 21]]]

@[expose] def aslA : List (Perm (Fin 16)) :=
  [permOf 16 [[1, 4, 5], [2, 8, 10], [3, 12, 15], [6, 13, 11], [7, 9, 14]],
   permOf 16 [[0, 1, 5, 12, 6], [2, 9, 11, 3, 13], [4, 8, 15, 10, 7]]]

@[expose] def aslB : List (Perm (Fin 16)) :=
  [permOf 16 [[1, 4, 5], [2, 8, 10], [3, 12, 15], [6, 13, 11], [7, 9, 14]],
   permOf 16 [[0, 1, 8, 7, 11], [2, 15, 13, 3, 6], [4, 12, 10, 9, 14]]]

@[expose] def check : Bool :=
  sgPerms.map tabP == CFSG.Quasithin.H.MathieuLat.m23STabs &&
    closedH (yaGens.map RN.enc) (elts (RN.enc : Perm (Fin 23) → RN 23) 32 yaGens) &&
    (elts (RN.enc : Perm (Fin 23) → RN 23) 32 yaGens).size == 1920 &&
    closedH (ybGens.map RN.enc) (elts (RN.enc : Perm (Fin 23) → RN 23) 32 ybGens) &&
    (elts (RN.enc : Perm (Fin 23) → RN 23) 32 ybGens).size == 1920 &&
    !(elts (RN.enc : Perm (Fin 23) → RN 23) 32 yaGens).contains
      (RN.enc (evalW [m23PermA, m23PermB] wb)) &&
    aaGens.all (fun g => (elts (RN.enc : Perm (Fin 23) → RN 23) 32 yaGens).contains (RN.enc g)) &&
    abGens.all (fun g => (elts (RN.enc : Perm (Fin 23) → RN 23) 32 ybGens).contains (RN.enc g)) &&
    diagExtOK (RN.enc : Perm (Fin 23) → RN 23) (RN.enc : Perm (Fin 16) → RN 16) 32 aaGens aslA
      960 960 &&
    diagExtOK (RN.enc : Perm (Fin 23) → RN 23) (RN.enc : Perm (Fin 16) → RN 16) 32 abGens aslB
      960 960

end M23Asl
