
module

public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Mathieu.M23
public import CFSG.Sporadic.Schreier.Enumeration
public import CFSG.Sporadic.Schreier.M23Gens

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Mathieu

@[expose] def m23InvRepWords : List (List ℤ) :=
  [[1]]

@[expose] def m23InvReps : List (Equiv.Perm (Fin 23)) :=
  m23InvRepWords.map (evalCodes [m23PermA, m23PermB])

@[expose] def m23CentWords1 : List (List ℤ) :=
  [[-2, -1, -2, -1, -2, -1, -2, -2, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2,
    1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2], [-2, -2, -2, -1,
    -2, -1, -2, -1, -2, -2, -1, -2, -2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2], [-2, -1, -2, -2,
    -2, -1, -2, -2, -1, -2, -2, -2, -1, -2, -1, -2, -1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1,
    2, 1, 2, 1, 2, 2], [-2, -2, -2, -1, -2, -2, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -1,
    -2, -2, -2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2]]

@[expose] def m23CentChainWords1 : List (List ℤ) :=
  [[2], [-4, -4], [3, 4, 1], [-1, -3, -3, 1], [-6, -8]]

@[expose] def m23CentQ1 : RawSchreierDatum 23 :=
  certificate (by decide) (m23CentWords1.map (evalCodes [m23PermA, m23PermB])) m23CentChainWords1
    #v[2, 0, 5, 4] (by decide)

@[expose] def m23AutWords : List (List ℕ × ℕ) :=
  [([0, 1], 23), ([0, 1, 2, 3], 6), ([0, 1, 0, 1, 1, 0, 3], 4)]

end CFSG.Sporadic.Schreier
