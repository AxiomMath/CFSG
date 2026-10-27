module

public import CFSG.GH74.KGroups.M11Inputs
public meta import CFSG.GH74.KGroups.M11Inputs

public section

namespace Certificates.ONanSmallM11

@[expose] def m11x : Equiv.Perm (Fin 11) :=
  List.formPerm [2, 3, 4] * List.formPerm [5, 8, 10] * List.formPerm [6, 9, 7]

@[expose] def m11y : Equiv.Perm (Fin 11) :=
  List.formPerm [2, 5, 9] * List.formPerm [3, 8, 7] * List.formPerm [4, 10, 6]

@[expose] def m11s : Equiv.Perm (Fin 11) :=
  List.formPerm [0, 1] * List.formPerm [2, 4, 10, 3, 6, 9, 5, 7]

@[expose] def m11E : List (Equiv.Perm (Fin 11)) :=
  [1, m11x, m11x ^ 2, m11y, m11x * m11y, m11x ^ 2 * m11y, m11y ^ 2, m11x * m11y ^ 2,
    m11x ^ 2 * m11y ^ 2]

end Certificates.ONanSmallM11
