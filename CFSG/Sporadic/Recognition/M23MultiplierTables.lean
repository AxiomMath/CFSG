module

public import CFSG.Sporadic.Recognition.M23MultiplierInputs
public import CFSG.Sporadic.Bridge.M23Surj

public section

namespace CFSG.Sporadic.Recognition.M23Multiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Bridge.TwoGen.Native CFSG.Sporadic.Bridge.M23
  CFSG.Sporadic.Recognition.CoverTransfer CFSG.Sporadic.Recognition.CoverRecipe
open CFSG.Sporadic.Schreier (m23GenA m23GenB)

@[expose] def m23Ab (i : Fin 2) : CFSG.Blueprint.NativeSporadic.M23 :=
  img2 m23GenA m23GenB⁻¹ i.val

@[expose] def m23Gen (i : Fin 6) : CFSG.Blueprint.NativeSporadic.M23 :=
  FreeGroup.lift m23Ab (FreeGroup.mk (m23GenWords.getD i []))

theorem lift_m23Ab_eq_one (h : m23TabCheck = true) {w : List (Fin 2 × Bool)}
    (hw : w ∈ m23CheckWords) : FreeGroup.lift m23Ab (FreeGroup.mk w) = 1 :=
  lift_eq_one_of_relCheck (n := 23) (by norm_num) rep_a rep_a_inv rep_b_inv
    (by rw [inv_inv]; exact rep_b) h hw

theorem lift_m23Ab_eq_of_inv_mem (h : m23TabCheck = true) {u : List (Fin 2 × Bool)} {i : Fin 2}
    (hu : u ++ [(i, false)] ∈ m23CheckWords) :
    FreeGroup.lift m23Ab (FreeGroup.mk u) = m23Ab i :=
  lift_eq_of_inv_mem (n := 23) (by norm_num) rep_a rep_a_inv rep_b_inv
    (by rw [inv_inv]; exact rep_b) h hu

theorem lift_m23Gen_mk (r : List (Fin 6 × Bool)) :
    FreeGroup.lift m23Gen (FreeGroup.mk r) =
      FreeGroup.lift m23Ab (FreeGroup.mk (substWord m23GenWords r)) :=
  lift_mk_substWord m23Ab m23GenWords r

theorem substWord_rel_mem {r : List (Fin 6 × Bool)} (hr : r ∈ m23Rels) :
    substWord m23GenWords r ∈ m23CheckWords := by
  unfold m23CheckWords
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hr))

theorem substWord_comm_mem (i : Fin 6) :
    substWord m23GenWords ((i, false) :: m23CommWord i) ∈ m23CheckWords := by
  unfold m23CheckWords
  exact List.mem_append_left _
    (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩))

theorem lift_m23Gen_rels (h : m23TabCheck = true) :
    ∀ r ∈ wordSet m23Rels, FreeGroup.lift m23Gen r = 1 := by
  intro r hr
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hr
  rw [lift_m23Gen_mk]
  exact lift_m23Ab_eq_one h (substWord_rel_mem hv)

theorem lift_m23CommWord (h : m23TabCheck = true) (i : Fin 6) :
    FreeGroup.lift m23Gen (FreeGroup.mk (m23CommWord i)) = m23Gen i := by
  have h1 : FreeGroup.lift m23Gen (FreeGroup.mk ((i, false) :: m23CommWord i)) = 1 := by
    rw [lift_m23Gen_mk]
    exact lift_m23Ab_eq_one h (substWord_comm_mem i)
  rw [show FreeGroup.mk ((i, false) :: m23CommWord i) =
      (FreeGroup.of i)⁻¹ * FreeGroup.mk (m23CommWord i) from rfl, map_mul, map_inv,
    FreeGroup.lift_apply_of, inv_mul_eq_one] at h1
  exact h1.symm

theorem closure_m23Gen (h : m23TabCheck = true) : Subgroup.closure (Set.range m23Gen) = ⊤ := by
  refine closure_range_eq_top closure_gen (sA := m23SurjA) (sB := m23SurjB) ?_ ?_
  · rw [lift_m23Gen_mk]
    exact (lift_m23Ab_eq_of_inv_mem h (u := substWord m23GenWords m23SurjA) (i := 0) (by
      unfold m23CheckWords
      exact List.mem_append_right _ List.mem_cons_self)).symm
  · rw [lift_m23Gen_mk]
    exact (lift_m23Ab_eq_of_inv_mem h (u := substWord m23GenWords m23SurjB) (i := 1) (by
      unfold m23CheckWords
      exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))).symm

theorem card_m23 :
    Nat.card CFSG.Blueprint.NativeSporadic.M23 = 10200960 :=
  CFSG.Sporadic.Schreier.m23_card

end CFSG.Sporadic.Recognition.M23Multiplier
