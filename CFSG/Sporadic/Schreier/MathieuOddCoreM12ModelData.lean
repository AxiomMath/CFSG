module

public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Schreier.M12Data

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Sporadic.Mathieu

@[expose] def blockHom : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12) →* Equiv.Perm (Fin 24) :=
  (Equiv.permCongrHom finSumFinEquiv).toMonoidHom.comp
    (Equiv.Perm.sumCongrHom (Fin 12) (Fin 12))

@[expose] def m12bp : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 5, 3] * List.formPerm [1, 8, 2] *
    List.formPerm [4, 7, 9] * List.formPerm [6, 10, 11]

@[expose] def m12A1 : Equiv.Perm (Fin 24) := blockHom (m12gA, m12gA)

@[expose] def m12B1 : Equiv.Perm (Fin 24) := blockHom (m12gB, m12bp)

@[expose] def m12Sigma : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 12] * List.formPerm [1, 13] * List.formPerm [2, 14] * List.formPerm [3, 15] *
    List.formPerm [4, 16] * List.formPerm [5, 17] * List.formPerm [6, 18] * List.formPerm [7, 19] *
    List.formPerm [8, 20] * List.formPerm [9, 21] * List.formPerm [10, 22] * List.formPerm [11, 23]

@[expose] def m12D : RawSchreierDatum 24 :=
  certificate (by decide) [m12A1, m12B1] m12Words #v[0, 1, 2, 3, 4] (by decide)

@[expose] def m12SigmaCentWords : List (List ℤ) :=
  [[-2, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, 1, 2, 2, 1,
    2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2], [-2, -2, -1, -2, -2, -1, -2, -2, -1, -2,
    -1, -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2,
    1, 2, 2, 1, 2, 1, 2], [-2, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2,
    -1, -2, -2, -1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2]]

@[expose] def m12SigmaCentChainWords : List (List ℤ) :=
  [[-1, 2], [3, 1, 3], [-4, -5]]

@[expose] def m12SigmaCentQ : RawSchreierDatum 24 :=
  certificate (by decide) (m12SigmaCentWords.map (evalCodes [m12A1, m12B1]))
    m12SigmaCentChainWords #v[1, 0, 2] (by decide)

end CFSG.Sporadic.Schreier
