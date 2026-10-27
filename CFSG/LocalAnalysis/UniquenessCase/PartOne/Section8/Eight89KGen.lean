module

public import CFSG.CGT.T75JM.N6A6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

open Subgroup

theorem closure_eq_top_of_map {K Q : Type*} [Group K] [Group Q] (f : K →* Q) {x y z : K}
    (hker : f.ker = zpowers z) (hgen : closure ({f x, f y} : Set Q) = ⊤) :
    closure ({x, y, z} : Set K) = ⊤ := by
  have hmap : (closure ({x, y, z} : Set K)).map f = ⊤ := by
    rw [MonoidHom.map_closure, ← top_le_iff, ← hgen, Set.image_insert_eq, Set.image_insert_eq,
      Set.image_singleton]
    exact closure_mono (Set.insert_subset_insert (Set.singleton_subset_iff.2 (Set.mem_insert _ _)))
  have hle : f.ker ≤ closure ({x, y, z} : Set K) := by
    rw [hker, zpowers_le]
    exact subset_closure (by simp)
  rw [← comap_map_eq_self hle, hmap, comap_top]

theorem closure_a6_eq_top (hn : CFSG.CGT.T75JM.A6Nodup) :
    closure ({⟨CFSG.CGT.T75JM.a6x, CFSG.CGT.T75JM.a6x_mem⟩,
      ⟨CFSG.CGT.T75JM.a6y, CFSG.CGT.T75JM.a6y_mem⟩} : Set (alternatingGroup (Fin 6))) = ⊤ := by
  apply map_injective (alternatingGroup (Fin 6)).subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, range_subtype, Set.image_insert_eq,
    Set.image_singleton]
  exact CFSG.CGT.T75JM.a6_closure hn

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs
