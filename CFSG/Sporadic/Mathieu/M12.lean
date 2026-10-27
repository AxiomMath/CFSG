module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Sporadic.Mathieu.Simple
public import CFSG.Sporadic.Mathieu.M12Cert

public section

namespace CFSG.Sporadic.Mathieu

open CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Mathieu.Native

abbrev m12gA : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] * List.formPerm [5, 11]

abbrev m12gB : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] * List.formPerm [4, 11, 10] *
    List.formPerm [5, 9, 6]

theorem m12_eq : NativeSporadic.M12 = Subgroup.closure {m12gA, m12gB} := rfl

abbrev m12a : NativeSporadic.M12 :=
  ⟨m12gA, by rw [m12_eq]; exact Subgroup.subset_closure (Set.mem_insert _ _)⟩

abbrev m12b : NativeSporadic.M12 :=
  ⟨m12gB, by rw [m12_eq]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

theorem rep_m12a : Rep 12 m12Data.tA m12a := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem rep_m12b : Rep 12 m12Data.tB m12b := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem m12_hyp : Hyp NativeSporadic.M12 m12Data m12a m12b :=
  ⟨by norm_num, closure_pair_eq_top m12_eq _ _, rep_m12a, rep_m12b, m12_check⟩

theorem card_M12 : Nat.card NativeSporadic.M12 = 95040 := by
  rw [card_eq m12_hyp]
  rfl

theorem fam_m12_simplicity :
    Finite NativeSporadic.M12 ∧ Nontrivial NativeSporadic.M12 ∧
    IsSimpleGroup NativeSporadic.M12 := by
  have h : IsSimpleGroup NativeSporadic.M12 :=
    isSimpleGroup_of_check_duads m12_hyp (by decide) (by norm_num) (by norm_num [m12Data])
      (by norm_num [m12Data]) (by norm_num [m12Data]) (by decide) (by decide)
  exact ⟨inferInstance, h.toNontrivial, h⟩

end CFSG.Sporadic.Mathieu
