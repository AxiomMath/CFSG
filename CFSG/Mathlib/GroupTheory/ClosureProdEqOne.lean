module

public import Mathlib.Algebra.Group.Subgroup.Finite

public section

theorem List.mem_closure_of_prod_eq_one {M : Type*} [Group M] [DecidableEq M] {l : List M}
    (hnodup : l.Nodup) (hcomm : ∀ x ∈ l, ∀ y ∈ l, x * y = y * x) (hprod : l.prod = 1)
    {a : M} (ha : a ∈ l) :
    a ∈ Subgroup.closure ({x | x ∈ l} \ {a}) := by
  have h := List.prod_erase_of_comm ha hcomm
  have h' : a = ((l.erase a).prod)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [h, hprod])
  rw [h']
  exact Subgroup.inv_mem _ (Subgroup.list_prod_mem _ (fun x hx => by
    obtain ⟨hxne, hxmem⟩ := hnodup.mem_erase_iff.mp hx
    exact Subgroup.subset_closure ⟨hxmem, by
      rw [Set.mem_singleton_iff]
      rwa [← h']⟩))

end
