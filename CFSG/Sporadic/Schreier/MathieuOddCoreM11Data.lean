module

public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Schreier.Enumeration

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Mathieu

@[expose] def m11InvRepWords : List (List ℤ) :=
  [[1]]

@[expose] def m11InvReps : List (Equiv.Perm (Fin 11)) :=
  m11InvRepWords.map (evalCodes [m11gA, m11gB])

@[expose] def m11CentWords1 : List (List ℤ) :=
  [[-2, -2, -2, -1, -2, -1, -2, -2, -2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2], [-2, -1, -2, -2, -2, -1, -2,
    -2, -1, -2, -1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2], [-2, -1, -2, -1, -2, -2, -1, -2, -1,
    -2, -2, -1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2], [-2, -2, -1, -2, -1, -2, -2, -1, -2, -2,
    -1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2]]

@[expose] def m11CentChainWords1 : List (List ℤ) :=
  [[2], [-1, 3], [-1, -3], [6, -1, 4, 1]]

@[expose] def m11CentQ1 : RawSchreierDatum 11 :=
  certificate (by decide) (m11CentWords1.map (evalCodes [m11gA, m11gB])) m11CentChainWords1
    #v[0, 1, 2] (by decide)

@[expose] def m11AutWords : List (List ℕ × ℕ) :=
  [([0, 1], 11), ([0, 1, 2, 3], 6), ([0, 1, 0, 1, 1, 0, 3], 3)]

end CFSG.Sporadic.Schreier
