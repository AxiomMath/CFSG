
module

public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.Enumeration

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Mathieu

@[expose] def m24InvRepWords : List (List ℤ) :=
  [[1], [1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1,
    -2, 1, 2, 1, 2, 1, -2]]

@[expose] def m24InvReps : List (Equiv.Perm (Fin 24)) :=
  m24InvRepWords.map (evalCodes [m24gA, m24gB])

@[expose] def m24CentWords1 : List (List ℤ) :=
  [[-2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1,
    -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2,
    1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2], [-2, -2, -1, -2,
    -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -2,
    -1, -2, -2, -1, -2, -2, -1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2,
    2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2], [-2, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -1,
    -2, -2, -1, -2, -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2,
    -1, -2, -1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1,
    2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2]]

@[expose] def m24CentChainWords1 : List (List ℤ) :=
  [[-2, 3, 1], [-1, -1, 4, 1], [-4, -4, -5, -1, -2, -2, 1], [-4, -4, 6, -1, 3, -4, 1], [4, 5, 2, 7,
    1]]

@[expose] def m24CentQ1 : RawSchreierDatum 24 :=
  certificate (by decide) (m24CentWords1.map (evalCodes [m24gA, m24gB])) m24CentChainWords1
    #v[0, 1, 2] (by decide)

@[expose] def m24CentWords2 : List (List ℤ) :=
  [[-2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2, -2, -1,
    -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2,
    2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2], [-2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -2,
    -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2,
    -1, -2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1,
    2, 2, 1, 2, 2, 1, 2, 1, 2]]

@[expose] def m24CentChainWords2 : List (List ℤ) :=
  [[1, -2], [3, 3, -1, -1, -2, 1], [-3, -3, -1, -2, 1, 2], [4, -5, 3, -4, -1, -3, 5, 1], [4, 5, -3,
    -6, -4, -1, -2, -5, 1]]

@[expose] def m24CentQ2 : RawSchreierDatum 24 :=
  certificate (by decide) (m24CentWords2.map (evalCodes [m24gA, m24gB])) m24CentChainWords2
    #v[1, 0, 2, 3] (by decide)

@[expose] def m24AutWords : List (List ℕ × ℕ) :=
  [([0, 1], 23), ([0, 1, 2, 3], 12), ([0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 3], 5)]

end CFSG.Sporadic.Schreier
