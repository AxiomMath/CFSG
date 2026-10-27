module

public import CFSG.Sporadic.J4.QTData

public section

namespace CFSG.Sporadic.J4.QT

@[expose] def rel01 : List (List Int) := [
    [-1, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 1],
    [-2, 1, 1, -2, 1, 1, -2, 1, 1, -2, 1, 1, -2, 1, 1, -2, 1, 1],
    [-2, 1, -2, -2, -1, 2, -1, -1, 2, -1, -2, 1, -1, -1, -1, 2, 2, 1, 1, 2, -1]]

@[expose] def rel02 : List (List Int) := [
    [-3, -1, 3, 1, -3, -1, 3, 1, -3, -1, 3, 1, -3, -1, 3, 1],
    [-3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3],
    [1, -3, -1, 3, 1, 1, 3, -1, -3, -3, -3, 1, -3, -3, -1, -3, -3, -3, -1, 3]]

@[expose] def relMix : List (List Int) := [
    [1, 1, 2, 1, -3, 2, 2, 1, -3, 2, 2, 1, -3, 2, -1, -1]]

end CFSG.Sporadic.J4.QT
