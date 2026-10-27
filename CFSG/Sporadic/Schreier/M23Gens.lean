module

public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Blueprint

abbrev m23PermA : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] * List.formPerm [8, 9] *
    List.formPerm [12, 13] * List.formPerm [14, 15] * List.formPerm [18, 19] *
    List.formPerm [20, 21]

abbrev m23PermB : Equiv.Perm (Fin 23) :=
  List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] * List.formPerm [3, 4, 7, 22] *
    List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] * List.formPerm [14, 16]

theorem m23_eq_closure : NativeSporadic.M23 = Subgroup.closure {m23PermA, m23PermB} := rfl

abbrev m23GenA : NativeSporadic.M23 :=
  ⟨m23PermA, by rw [m23_eq_closure]; exact Subgroup.subset_closure (Set.mem_insert _ _)⟩

abbrev m23GenB : NativeSporadic.M23 :=
  ⟨m23PermB, by rw [m23_eq_closure]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

end CFSG.Sporadic.Schreier
