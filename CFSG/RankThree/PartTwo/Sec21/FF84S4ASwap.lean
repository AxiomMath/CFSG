module

public import CFSG.RankThree.PartTwo.Sec21.FF84S47Items
import CFSG.RankThree.PartTwo.Sec21.FF84S4APiStar

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8 A8s)

private theorem closure_pair_inv_left (x y : P8) :
    Subgroup.closure ({x⁻¹, y} : Set P8) = Subgroup.closure {x, y} := by
  have hx : x ∈ Subgroup.closure ({x, y} : Set P8) := Subgroup.subset_closure (Set.mem_insert _ _)
  have hy : y ∈ Subgroup.closure ({x, y} : Set P8) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hx' : x⁻¹ ∈ Subgroup.closure ({x⁻¹, y} : Set P8) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hy' : y ∈ Subgroup.closure ({x⁻¹, y} : Set P8) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  apply le_antisymm
  · exact (Subgroup.closure_le _).2
      (Set.insert_subset_iff.2 ⟨inv_mem hx, Set.singleton_subset_iff.2 hy⟩)
  · refine (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨?_, Set.singleton_subset_iff.2 hy'⟩)
    have := inv_mem hx'
    rwa [inv_inv] at this

private theorem closure_pair_mul_right (x y : P8) :
    Subgroup.closure ({x, x * y} : Set P8) = Subgroup.closure {x, y} := by
  have hx : x ∈ Subgroup.closure ({x, y} : Set P8) := Subgroup.subset_closure (Set.mem_insert _ _)
  have hy : y ∈ Subgroup.closure ({x, y} : Set P8) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hx' : x ∈ Subgroup.closure ({x, x * y} : Set P8) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hxy' : x * y ∈ Subgroup.closure ({x, x * y} : Set P8) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  apply le_antisymm
  · exact (Subgroup.closure_le _).2
      (Set.insert_subset_iff.2 ⟨hx, Set.singleton_subset_iff.2 (mul_mem hx hy)⟩)
  · refine (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨hx', Set.singleton_subset_iff.2 ?_⟩)
    have h := mul_mem (inv_mem hx') hxy'
    rwa [inv_mul_cancel_left] at h

theorem A_swap_holds : A_swap_stmt := by
  set g : P8 := Equiv.swap 0 1 * Equiv.swap 6 7 with hg
  refine ⟨g, Subgroup.mem_inf.mpr ⟨?_, swap_mul_swap_mem_A8 (by decide) (by decide)⟩, ?_⟩
  ·
    show g ∈ Subgroup.normalizer (Pm : Set P8)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change conjBy g (Subgroup.closure ({cc, dd} : Set P8)) = Subgroup.closure {cc, dd}
    rw [conjBy_closure_pair, show g * cc * g⁻¹ = cc⁻¹ by decide,
      show g * dd * g⁻¹ = dd by decide, closure_pair_inv_left]
  · change (v4 3 4 5 6 ⊔ v4 0 1 2 7).map (MulAut.conj g).toMonoidHom = v4 3 4 5 7 ⊔ v4 0 1 2 6
    rw [Subgroup.map_sup]
    change conjBy g (v4 3 4 5 6) ⊔ conjBy g (v4 0 1 2 7) = v4 3 4 5 7 ⊔ v4 0 1 2 6
    rw [v4, v4, v4, v4, conjBy_closure_pair, conjBy_closure_pair,
      show g * (Equiv.swap 3 4 * Equiv.swap 5 6) * g⁻¹ = Equiv.swap 3 4 * Equiv.swap 5 7 by decide,
      show g * (Equiv.swap 3 5 * Equiv.swap 4 6) * g⁻¹ = Equiv.swap 3 5 * Equiv.swap 4 7 by decide,
      show g * (Equiv.swap 0 1 * Equiv.swap 2 7) * g⁻¹ = Equiv.swap 0 1 * Equiv.swap 2 6 by decide,
      show g * (Equiv.swap 0 2 * Equiv.swap 1 7) * g⁻¹ =
        (Equiv.swap 0 1 * Equiv.swap 2 6) * (Equiv.swap 0 2 * Equiv.swap 1 6) by decide,
      closure_pair_mul_right]

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
