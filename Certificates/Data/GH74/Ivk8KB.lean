module

public import Certificates.Data.GH74.Ivk8L34
public meta import Certificates.Data.GH74.Ivk8L34

public section

namespace Certificates.Ivk8KB

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier
  CFSG.Certificates Certificates.Odd87F3 Certificates.Ivk8Weak Certificates.Ivk8Weak.L34

@[expose] def wordR4 : List ℤ := [5, 6]

@[expose] def wordD1 : List ℤ := [1, 2, -1, 2, 1, 2, 1, 2, -1, 2]

@[expose] def wordD4 : List ℤ := [3, -1, 3, -1, 2, 1, 2, 1, 3]

@[expose] def wordsE : List (List ℤ) :=
  [[1, 2, 1, 2, 3, 1, 3, 1, 2, 1, 2, 3, 1, 3, 1, 2],
   [1, 2, 1, 3, 1, 2, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2],
   [1], [2, -1, 2, 3, -1, 3, -1, 2, -1, 2, 3, -1, 3, -1, 2],
   [2, -1, 3, -1, 2, 3, -1, 2, -1, 3, -1, 2, 3, -1, 2], [-1],
   [2, 1, 3, 1, 2, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2], [2, 1, 2, 3, 1, 3, 1, 2, 1, 2, 3, 1, 3, 1, 2]]

end Certificates.Ivk8KB
