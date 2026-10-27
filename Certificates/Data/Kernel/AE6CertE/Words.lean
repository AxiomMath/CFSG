module

public import Init

public section

namespace Certificates.AE6CertEK

@[expose] def dU : List (List Int) := [[-2, 3, 2], [-5, 4, 5], [-4, -2, 4, 2]]

@[expose] def dV0 : List (List Int) :=
  [[-2, 4, 2], [-8, 6, 8], [-6, -2, 6, 2], [-5, 3, 5], [-7, 3, 7]]

@[expose] def dV1 : List (List Int) :=
  [[-3, 5, 3], [-8, 7, 8], [-7, -3, 7, 3], [-6, 4, 6], [-1, -2, -4, 9, 2, 1],
    [-7, -9, -12, -3, 12, 3], [-10, -13, -7, -12, -11, 13, 11]]

@[expose] def dV2 : List (List Int) :=
  [[-3, 5, 3], [-8, 6, 8], [-6, -3, 6, 3], [-7, 4, 7], [-1, -2, -4, 9, 2, 1],
    [-6, -9, -12, -3, 12, 3], [-11, -10, 13, 11]]

@[expose] def dP1 : List (List Int) :=
  [[-3, 4, 3], [-6, 5, 6], [-5, -3, 5, 3], [-5, -7, -4, -6, -1, -6, -1, -2, 8, 1, 6, 1]]

@[expose] def dP3 : List (List Int) := [[-2, 4, 2], [-6, 5, 6], [-5, -2, 5, 2]]

@[expose] def dP5 : List (List Int) := [[-2, 3, 2], [-6, 5, 6], [-5, -2, 5, 2]]

@[expose] def dP7 : List (List Int) := [[-2, 3, 2], [-6, 4, 6], [-4, -2, 4, 2]]

@[expose] def dP57 : List (List Int) := [[-2, 3, 2], [-7, 5, 7], [-5, -2, 5, 2]]

@[expose] def dP15 : List (List Int) :=
  [[-3, 4, 3], [-7, 6, 7], [-6, -3, 6, 3], [-6, -8, -4, -7, -1, -7, -1, -2, 9, 1, 7, 1]]

@[expose] def dP17 : List (List Int) :=
  [[-3, 4, 3], [-7, 5, 7], [-5, -3, 5, 3], [-5, -8, -4, -7, -1, -7, -1, -2, 9, 1, 7, 1]]

end Certificates.AE6CertEK
