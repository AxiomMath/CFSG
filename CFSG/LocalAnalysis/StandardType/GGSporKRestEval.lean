module

public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.StandardType.SporadicShape

@[expose] def sporKRestEval {K : Type} [Group K] (gens : List K) (w : List ℤ) : K :=
  (w.map fun l =>
    if 0 < l then gens.getD (l.toNat - 1) 1 else (gens.getD ((-l).toNat - 1) 1)⁻¹).prod

@[expose] def sporKRestParse (s : String) : List ℤ :=
  (s.splitOn " ").filterMap String.toInt?

private theorem ggSporKRestEval_getD_mem {K : Type} [Group K] (gens : List K) (H : Subgroup K)
    (h : ∀ g ∈ gens, g ∈ H) (n : ℕ) : gens.getD n 1 ∈ H := by
  rw [List.getD_eq_getElem?_getD]
  cases hg : gens[n]? with
  | none => simpa using H.one_mem
  | some g =>
      simp only [hg, Option.getD_some]
      exact h g (List.mem_iff_getElem?.mpr ⟨n, hg⟩)

private theorem ggSporKRestEval_getD_map {K G : Type} [Group K] [Group G] (f : K →* G)
    (gens : List K) (n : ℕ) : (gens.map f).getD n 1 = f (gens.getD n 1) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases hg : gens[n]? <;> simp

theorem sporKRestEval_mem {K : Type} [Group K] (gens : List K) (w : List ℤ) (H : Subgroup K)
    (h : ∀ g ∈ gens, g ∈ H) : sporKRestEval gens w ∈ H := by
  unfold sporKRestEval
  apply Subgroup.list_prod_mem H
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨l, _hl, rfl⟩ := hx
  split_ifs with hl
  · exact ggSporKRestEval_getD_mem gens H h (l.toNat - 1)
  · exact H.inv_mem (ggSporKRestEval_getD_mem gens H h ((-l).toNat - 1))

theorem sporKRestEval_map {K G : Type} [Group K] [Group G] (f : K →* G) (gens : List K)
    (w : List ℤ) : f (sporKRestEval gens w) = sporKRestEval (gens.map f) w := by
  unfold sporKRestEval
  rw [map_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro l _
  change f (if 0 < l then gens.getD (l.toNat - 1) 1 else (gens.getD ((-l).toNat - 1) 1)⁻¹) =
    (if 0 < l then (gens.map f).getD (l.toNat - 1) 1
      else ((gens.map f).getD ((-l).toNat - 1) 1)⁻¹)
  split_ifs with hl
  · exact (ggSporKRestEval_getD_map f gens (l.toNat - 1)).symm
  · rw [map_inv, ← ggSporKRestEval_getD_map f gens ((-l).toNat - 1)]

end CFSG.StandardType.SporadicShape
