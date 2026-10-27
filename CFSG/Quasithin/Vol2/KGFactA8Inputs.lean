module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermEnc

public section

namespace CFSG.Quasithin.H13.KGA8

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

@[expose] def sGens : List (Perm (Fin 8)) :=
  [permOf 8 [[2, 3], [6, 7]], permOf 8 [[0, 2], [1, 3]], permOf 8 [[0, 4], [1, 5], [2, 6], [3, 7]]]

@[expose] def mGens : List (Perm (Fin 8)) :=
  [permOf 8 [[0, 1, 2]], permOf 8 [[0, 1, 3]], permOf 8 [[0, 1, 4]], permOf 8 [[0, 1, 5]],
    permOf 8 [[0, 1, 6]], permOf 8 [[0, 1, 7]]]

@[expose] def patterns : List (List Bool) :=
  [[true, false, false], [false, true, false], [true, true, false], [false, false, true],
    [true, false, true], [false, true, true], [true, true, true]]

end CFSG.Quasithin.H13.KGA8
