module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Sporadic.Mathieu.Simple
public import CFSG.Sporadic.Mathieu.M24Cert

public section

namespace CFSG.Sporadic.Mathieu

open CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Mathieu.Native

abbrev m24gA : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 3] * List.formPerm [1, 6] * List.formPerm [2, 16] * List.formPerm [4, 12] *
    List.formPerm [5, 8] * List.formPerm [7, 14] * List.formPerm [9, 18] * List.formPerm [10, 17] *
    List.formPerm [11, 20] * List.formPerm [13, 15] * List.formPerm [19, 23] *
    List.formPerm [21, 22]

abbrev m24gB : Equiv.Perm (Fin 24) :=
  List.formPerm [0, 3, 5] * List.formPerm [1, 20, 13] * List.formPerm [2, 8, 14] *
    List.formPerm [4, 17, 9] * List.formPerm [12, 16, 15] * List.formPerm [18, 23, 22]

theorem m24_eq : NativeSporadic.M24 = Subgroup.closure {m24gA, m24gB} := rfl

abbrev m24a : NativeSporadic.M24 :=
  ⟨m24gA, by rw [m24_eq]; exact Subgroup.subset_closure (Set.mem_insert _ _)⟩

abbrev m24b : NativeSporadic.M24 :=
  ⟨m24gB, by rw [m24_eq]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

theorem rep_m24a : Rep 24 m24Data.tA m24a := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem rep_m24b : Rep 24 m24Data.tB m24b := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem m24_hyp : Hyp NativeSporadic.M24 m24Data m24a m24b :=
  ⟨by norm_num, closure_pair_eq_top m24_eq _ _, rep_m24a, rep_m24b, m24_check⟩

theorem card_M24 : Nat.card NativeSporadic.M24 = 244823040 := by
  rw [card_eq m24_hyp]
  rfl

theorem fam_m24_simplicity :
    Finite NativeSporadic.M24 ∧ Nontrivial NativeSporadic.M24 ∧
    IsSimpleGroup NativeSporadic.M24 := by
  have h : IsSimpleGroup NativeSporadic.M24 :=
    isSimpleGroup_of_check_duads m24_hyp (by decide) (by norm_num) (by norm_num [m24Data])
      (by norm_num [m24Data]) (by norm_num [m24Data]) (by decide) (by decide)
  exact ⟨inferInstance, h.toNontrivial, h⟩

end CFSG.Sporadic.Mathieu
