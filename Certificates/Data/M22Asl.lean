module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermExtCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM22DataInputs

public section

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat
open PermLat

namespace M22Asl

@[expose] def aslGens : List (Perm (Fin 16)) :=
  [permOf 16 [[1, 4, 5], [2, 8, 10], [3, 12, 15], [6, 13, 11], [7, 9, 14]],
   permOf 16 [[0, 4, 14, 5, 2], [1, 8, 11, 3, 12], [6, 10, 15, 9, 7]]]

@[expose] def check : Bool :=
  diagExtOK (RN.enc : Perm (Fin 22) → RN 22) (RN.enc : Perm (Fin 16) → RN 16) 64 p5Gens aslGens
    960 960

end M22Asl
