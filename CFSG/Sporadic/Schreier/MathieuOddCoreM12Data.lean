module

public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Schreier.Enumeration

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Mathieu

@[expose] def m12InvRepWords : List (List ℤ) :=
  [[1], [1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2]]

@[expose] def m12InvReps : List (Equiv.Perm (Fin 12)) :=
  m12InvRepWords.map (evalCodes [m12gA, m12gB])

@[expose] def m12CentWords1 : List (List ℤ) :=
  [[-2, -2, -1, -2, -2, -1, -2, -2, -1, -2, -2, -1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2], [-2,
    -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, 1, 2, 1, 2, 1,
    2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2], [-2, -1, -2, -2, -1, -2, -2, -1, -2, -1,
    -2, -2, -1, -2, -2, -1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2], [-2, -1, -2,
    -1, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, 2, 1, 2, 2, 1, 2, 1, 2,
    1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2]]

@[expose] def m12CentChainWords1 : List (List ℤ) :=
  [[-4, -3], [-4, 2, 1], [5, -6], [-6, -2, -3, 1]]

@[expose] def m12CentQ1 : RawSchreierDatum 12 :=
  certificate (by decide) (m12CentWords1.map (evalCodes [m12gA, m12gB])) m12CentChainWords1
    #v[0, 1, 2] (by decide)

@[expose] def m12CentWords2 : List (List ℤ) :=
  [[-1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2, 1, 2, 2, 1,
    2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2], [-2, -1, -2, -1, -2, -1, -2, -2, -1, -2,
    -1, -2, -1, -2, -2, -1, -2, -1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1], [
    -1, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1,
    2, 1, 2, 1, 2, 1, 2, 1]]

@[expose] def m12CentChainWords2 : List (List ℤ) :=
  [[-3, -2], [-2, -3]]

@[expose] def m12CentQ2 : RawSchreierDatum 12 :=
  certificate (by decide) (m12CentWords2.map (evalCodes [m12gA, m12gB])) m12CentChainWords2
    #v[0, 1, 2] (by decide)

@[expose] def m12AutWords : List (List ℕ × ℕ) :=
  [([0, 1], 11), ([0, 1, 2, 3], 6), ([0, 1, 0, 1, 0, 3], 6)]

end CFSG.Sporadic.Schreier
