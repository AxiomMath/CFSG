module

public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open Equiv Equiv.Perm Subgroup

@[expose] def a9fS : Finset (Fin 9) := {3, 4, 5, 6, 7, 8}

@[expose] def a9fAlt6 : Subgroup (alternatingGroup (Fin 9)) :=
  (alternatingGroup.ofSubtype a9fS).range

@[expose] def a9fT0 : alternatingGroup (Fin 9) :=
  ⟨List.formPerm [(0 : Fin 9), 1, 2], Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def a9fT1 : alternatingGroup (Fin 9) :=
  ⟨List.formPerm [(3 : Fin 9), 4, 5], Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def a9fT2 : alternatingGroup (Fin 9) :=
  ⟨List.formPerm [(6 : Fin 9), 7, 8], Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def a9fE0 : Subgroup (alternatingGroup (Fin 9)) :=
  Subgroup.zpowers a9fT1 ⊔ Subgroup.zpowers a9fT2

@[expose] def a9fW0 : alternatingGroup (Fin 9) :=
  ⟨swap 0 3 * swap 1 4 * swap 2 5 * swap 6 7, Perm.mem_alternatingGroup.mpr (by decide)⟩

end CFSG.RankThree.PartTwo.Sec8.Hering611
