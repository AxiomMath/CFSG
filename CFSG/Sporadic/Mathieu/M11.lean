module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Sporadic.Mathieu.Simple
public import CFSG.Sporadic.Mathieu.M11Cert

public section

namespace CFSG.Sporadic.Mathieu

open CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Mathieu.Native

abbrev m11gA : Equiv.Perm (Fin 11) :=
  List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] * List.formPerm [7, 8]

abbrev m11gB : Equiv.Perm (Fin 11) := List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8]

theorem m11_eq : NativeSporadic.M11 = Subgroup.closure {m11gA, m11gB} := rfl

abbrev m11a : NativeSporadic.M11 :=
  ⟨m11gA, by rw [m11_eq]; exact Subgroup.subset_closure (Set.mem_insert _ _)⟩

abbrev m11b : NativeSporadic.M11 :=
  ⟨m11gB, by rw [m11_eq]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

theorem rep_m11a : Rep 11 m11Data.tA m11a := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem rep_m11b : Rep 11 m11Data.tB m11b := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem m11_hyp : Hyp NativeSporadic.M11 m11Data m11a m11b :=
  ⟨by norm_num, closure_pair_eq_top m11_eq _ _, rep_m11a, rep_m11b, m11_check⟩

theorem card_M11 : Nat.card NativeSporadic.M11 = 7920 := by
  rw [card_eq m11_hyp]
  rfl

theorem fam_m11_simplicity :
    Finite NativeSporadic.M11 ∧ Nontrivial NativeSporadic.M11 ∧
    IsSimpleGroup NativeSporadic.M11 := by
  have h : IsSimpleGroup NativeSporadic.M11 :=
    isSimpleGroup_of_check m11_hyp (by decide) (by norm_num) (by norm_num [m11Data])
      (by norm_num [m11Data]) (by norm_num [m11Data]) (by decide) (by decide)
  exact ⟨inferInstance, h.toNontrivial, h⟩

end CFSG.Sporadic.Mathieu
