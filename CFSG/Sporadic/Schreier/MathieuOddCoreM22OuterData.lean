module

public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Schreier.Enumeration

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Mathieu

@[expose] def m22Delta : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 13] * List.formPerm [1, 4] * List.formPerm [2, 3] * List.formPerm [5, 18] *
    List.formPerm [6, 10] * List.formPerm [7, 12] * List.formPerm [8, 11] * List.formPerm [9, 21] *
    List.formPerm [14, 19] * List.formPerm [15, 20] * List.formPerm [16, 17]

@[expose] def m22OutRepWords : List (List ℤ) :=
  [[], [2, -1, 2, 1, 2, -1, 2, 1, -1, 2, -2, -1, 2, 2, -1, -2, -2, 2, -1, -1, -1, 2, 1, 2, 1, -2,
    -2, 2, 1, -2]]

@[expose] def m22OutReps : List (Equiv.Perm (Fin 22)) :=
  m22OutRepWords.map fun w => evalCodes [m22gA, m22gB] w * m22Delta

@[expose] def m22OutCentWords1 : List (List ℤ) :=
  [[-2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -2, -2, -1, -2, -2, -2, -1, 2, 1, 2, 1, 2, 1, 2, 2, 1,
    2, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1], [-1, -2, -2, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2,
    -1, -2, -1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1], [-2, -1, -2, -1, -2,
    -1, -2, -1, -2, -2, -2, -1, -2, -1, -2, -2, -2, -1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2,
    2, 2, 1, 2]]

@[expose] def m22OutCentChainWords1 : List (List ℤ) :=
  [[2], [-1, 3], [-2, -5, -2, -5, -5, -1, -1], [-5, -2, 5, -1, 2, 1], [-2, 3, 1]]

@[expose] def m22OutCentQ1 : RawSchreierDatum 22 :=
  certificate (by decide) (m22OutCentWords1.map (evalCodes [m22gA, m22gB]))
    m22OutCentChainWords1 #v[0, 1, 2] (by decide)

@[expose] def m22OutCentWords2 : List (List ℤ) :=
  [[-2, -2, -2, -1, -2, -2, -2, -1, -2, -1, -2, -1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 1], [-1,
    -2, -2, -2, -1, 2, 1, 2, 1, 2, 1, 2, 2, 1], [-2, -1, -2, -1, -2, -2, -1, 2, 2, 2, 1, 2, 1, 2, 2
    ]]

@[expose] def m22OutCentChainWords2 : List (List ℤ) :=
  [[2], [-1, -1], [-1, 2, 1], [-2, -6, -1, -6, 1], [-2, -5, 2, -1, -3, 1, 3]]

@[expose] def m22OutCentQ2 : RawSchreierDatum 22 :=
  certificate (by decide) (m22OutCentWords2.map (evalCodes [m22gA, m22gB]))
    m22OutCentChainWords2 #v[0, 1, 2] (by decide)

end CFSG.Sporadic.Schreier
