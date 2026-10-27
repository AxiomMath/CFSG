module

public import CFSG.Sporadic.M23.M23Simplicity
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.Mathieu

open CFSG.Blueprint

theorem m23_gen_a : (List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [6, 7] *
    List.formPerm [8, 9] * List.formPerm [12, 13] * List.formPerm [14, 15] *
    List.formPerm [18, 19] * List.formPerm [20, 21] : Equiv.Perm (Fin 23)) =
      CFSG.M23.M23Group.a := by
  decide

theorem m23_gen_b : (List.formPerm [0, 15, 10, 2] * List.formPerm [1, 8, 20, 11] *
    List.formPerm [3, 4, 7, 22] * List.formPerm [5, 21, 13, 17] * List.formPerm [12, 19] *
    List.formPerm [14, 16] : Equiv.Perm (Fin 23)) = CFSG.M23.M23Group.b := by
  decide

theorem nativeM23_eq : NativeSporadic.M23 = CFSG.M23.M23Group.M23Gen := by
  rw [NativeSporadic.M23, CFSG.M23.M23Group.M23Gen, m23_gen_a, m23_gen_b]

theorem fam_m23_simplicity :
    Finite NativeSporadic.M23 ∧ Nontrivial NativeSporadic.M23 ∧
    IsSimpleGroup NativeSporadic.M23 := by
  have h : IsSimpleGroup NativeSporadic.M23 := by
    rw [nativeM23_eq]
    exact CFSG.M23.M23Group.isSimpleGroup_H0
  exact ⟨inferInstance, h.toNontrivial, h⟩

end CFSG.Sporadic.Mathieu
