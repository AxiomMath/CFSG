module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Sporadic.Mathieu.Simple
public import CFSG.Sporadic.Mathieu.M22Cert

public section

namespace CFSG.Sporadic.Mathieu

open CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Mathieu.Native

abbrev m22gA : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] *
    List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13]

abbrev m22gB : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] *
    List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18]

theorem m22_eq : NativeSporadic.M22 = Subgroup.closure {m22gA, m22gB} := rfl

abbrev m22a : NativeSporadic.M22 :=
  ⟨m22gA, by rw [m22_eq]; exact Subgroup.subset_closure (Set.mem_insert _ _)⟩

abbrev m22b : NativeSporadic.M22 :=
  ⟨m22gB, by rw [m22_eq]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

theorem rep_m22a : Rep 22 m22Data.tA m22a := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem rep_m22b : Rep 22 m22Data.tB m22b := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem m22_hyp : Hyp NativeSporadic.M22 m22Data m22a m22b :=
  ⟨by norm_num, closure_pair_eq_top m22_eq _ _, rep_m22a, rep_m22b, m22_check⟩

theorem card_M22 : Nat.card NativeSporadic.M22 = 443520 := by
  rw [card_eq m22_hyp]
  rfl

theorem fam_m22_simplicity :
    Finite NativeSporadic.M22 ∧ Nontrivial NativeSporadic.M22 ∧
    IsSimpleGroup NativeSporadic.M22 := by
  have h : IsSimpleGroup NativeSporadic.M22 :=
    isSimpleGroup_of_check m22_hyp (by decide) (by norm_num) (by norm_num [m22Data])
      (by norm_num [m22Data]) (by norm_num [m22Data]) (by decide) (by decide)
  exact ⟨inferInstance, h.toNontrivial, h⟩

end CFSG.Sporadic.Mathieu
