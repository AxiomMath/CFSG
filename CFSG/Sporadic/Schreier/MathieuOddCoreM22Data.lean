module

public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Schreier.Enumeration

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Mathieu

@[expose] def m22InvRepWords : List (List ℤ) :=
  [[1]]

@[expose] def m22InvReps : List (Equiv.Perm (Fin 22)) :=
  m22InvRepWords.map (evalCodes [m22gA, m22gB])

@[expose] def m22CentWords1 : List (List ℤ) :=
  [[-2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -2, -2, 1, 2, 2, 1, 2, 2, 1, 2, 1,
    2, 2, 1, 2, 1, 2, 1, 2, 1, 2], [-2, -1, -2, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, 1, 2, 2, 2,
    1, 2, 2, 1, 2, 1, 2, 2, 2], [-2, -1, -2, -2, -2, -1, -2, -2, -2, -1, -2, -2, -2, -1, -2, -1,
    -2, -2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2]]

@[expose] def m22CentChainWords1 : List (List ℤ) :=
  [[2], [-2, -1, 2, 1], [-3, -3, -2, 3]]

@[expose] def m22CentQ1 : RawSchreierDatum 22 :=
  certificate (by decide) (m22CentWords1.map (evalCodes [m22gA, m22gB])) m22CentChainWords1
    #v[0, 1, 2] (by decide)

@[expose] def m22AutWords : List (List ℕ × ℕ) :=
  [([0, 1], 11), ([0, 1, 2, 3], 6), ([0, 1, 1], 5)]

end CFSG.Sporadic.Schreier
