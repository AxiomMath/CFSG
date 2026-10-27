module

public import CFSG.Sporadic.Recognition.M22MultiplierInputs
public import CFSG.Sporadic.Recognition.CoverCyclic
public import CFSG.Sporadic.Mathieu.M22

public section

namespace CFSG.Sporadic.Recognition.M22Multiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Bridge.TwoGen.Native CFSG.Sporadic.Recognition.CoverRecipe
  CFSG.Sporadic.Recognition.CoverCyclic CFSG.Sporadic.Recognition.CoverTransfer
open CFSG.Sporadic.Mathieu (m22a m22b m22_eq card_M22 closure_pair_eq_top)

theorem rep_a : CFSG.Sporadic.Th.Rep 22 tabA m22a := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem rep_b : CFSG.Sporadic.Th.Rep 22 tabB m22b := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem rep_a_inv : CFSG.Sporadic.Th.Rep 22 tabA m22a⁻¹ := by
  unfold CFSG.Sporadic.Th.Rep
  decide

theorem rep_b_inv : CFSG.Sporadic.Th.Rep 22 tabBi m22b⁻¹ := by
  unfold CFSG.Sporadic.Th.Rep
  decide

@[expose] def m22Ab (i : Fin 2) : CFSG.Blueprint.NativeSporadic.M22 := img2 m22a m22b i.val

@[expose] def m22Gen (i : Fin 2) : CFSG.Blueprint.NativeSporadic.M22 :=
  FreeGroup.lift m22Ab (FreeGroup.mk (m22GenWords.getD i []))

theorem lift_m22Ab_eq_one (h : m22TabCheck = true) {w : List (Fin 2 × Bool)}
    (hw : w ∈ m22CheckWords) : FreeGroup.lift m22Ab (FreeGroup.mk w) = 1 :=
  lift_eq_one_of_relCheck (n := 22) (by norm_num) rep_a rep_a_inv rep_b rep_b_inv h hw

theorem lift_m22Ab_eq_of_inv_mem (h : m22TabCheck = true) {u : List (Fin 2 × Bool)} {i : Fin 2}
    (hu : u ++ [(i, false)] ∈ m22CheckWords) :
    FreeGroup.lift m22Ab (FreeGroup.mk u) = m22Ab i :=
  lift_eq_of_inv_mem (n := 22) (by norm_num) rep_a rep_a_inv rep_b rep_b_inv h hu

theorem lift_m22Gen_mk (r : List (Fin 2 × Bool)) :
    FreeGroup.lift m22Gen (FreeGroup.mk r) =
      FreeGroup.lift m22Ab (FreeGroup.mk (substWord m22GenWords r)) :=
  lift_mk_substWord m22Ab m22GenWords r

theorem substWord_rel_mem {r : List (Fin 2 × Bool)} (hr : r ∈ m22Rels) :
    substWord m22GenWords r ∈ m22CheckWords := by
  unfold m22CheckWords
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hr))

theorem substWord_comm_mem (i : Fin 2) :
    substWord m22GenWords ((i, false) :: m22CommWord i) ∈ m22CheckWords := by
  unfold m22CheckWords
  exact List.mem_append_left _
    (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩))

theorem lift_m22Gen_rels (h : m22TabCheck = true) :
    ∀ r ∈ wordSet m22Rels, FreeGroup.lift m22Gen r = 1 := by
  intro r hr
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hr
  rw [lift_m22Gen_mk]
  exact lift_m22Ab_eq_one h (substWord_rel_mem hv)

theorem lift_m22CommWord (h : m22TabCheck = true) (i : Fin 2) :
    FreeGroup.lift m22Gen (FreeGroup.mk (m22CommWord i)) = m22Gen i := by
  have h1 : FreeGroup.lift m22Gen (FreeGroup.mk ((i, false) :: m22CommWord i)) = 1 := by
    rw [lift_m22Gen_mk]
    exact lift_m22Ab_eq_one h (substWord_comm_mem i)
  rw [show FreeGroup.mk ((i, false) :: m22CommWord i) =
      (FreeGroup.of i)⁻¹ * FreeGroup.mk (m22CommWord i) from rfl, map_mul, map_inv,
    FreeGroup.lift_apply_of, inv_mul_eq_one] at h1
  exact h1.symm

theorem closure_m22Gen (h : m22TabCheck = true) : Subgroup.closure (Set.range m22Gen) = ⊤ := by
  have hxy : Subgroup.closure ({m22a, m22b} : Set CFSG.Blueprint.NativeSporadic.M22) = ⊤ :=
    closure_pair_eq_top m22_eq _ _
  refine closure_range_eq_top hxy (sA := m22SurjA) (sB := m22SurjB) ?_ ?_
  · rw [lift_m22Gen_mk]
    exact (lift_m22Ab_eq_of_inv_mem h (u := substWord m22GenWords m22SurjA) (i := 0) (by
      unfold m22CheckWords
      exact List.mem_append_right _ List.mem_cons_self)).symm
  · rw [lift_m22Gen_mk]
    exact (lift_m22Ab_eq_of_inv_mem h (u := substWord m22GenWords m22SurjB) (i := 1) (by
      unfold m22CheckWords
      exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))).symm

theorem isPresentation_m22Gen (h : m22TabCheck = true)
    (hbd : Finite (PG 2 m22Rels) ∧ Nat.card (PG 2 m22Rels) ≤ 443520) :
    IsPresentation m22Gen (wordSet m22Rels) := by
  obtain ⟨hfin, hcard⟩ := hbd
  have : Finite (PresentedGroup (wordSet m22Rels)) := hfin
  exact IsPresentation.of_card_le (lift_m22Gen_rels h) (closure_m22Gen h)
    (hcard.trans (by rw [card_M22]))

theorem m22B11_mem : m22B11 ∈ m22Rels := by decide

theorem lift_m22B11 (h : m22TabCheck = true) :
    FreeGroup.lift m22Gen (FreeGroup.mk m22B11) = 1 :=
  lift_m22Gen_rels h _ (List.mem_map_of_mem m22B11_mem)

theorem center_cyclic_dvd_twelve (h : m22TabCheck = true)
    (hbd : Finite (PG 2 m22Rels) ∧ Nat.card (PG 2 m22Rels) ≤ 443520)
    (hcov : Finite (PG 2 m22Cover) ∧ Nat.card (PG 2 m22Cover) ≤ 5322240 ∧
      12 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ m22Cover.map FreeGroup.mk}
        (FreeGroup.mk m22B11)))
    {Q : Type} [Group Q] (hQ : Group.IsPerfect Q)
    (e : Q ⧸ Subgroup.center Q ≃* CFSG.Blueprint.NativeSporadic.M22) :
    IsCyclic (Subgroup.center Q) ∧ Nat.card (Subgroup.center Q) ∣ 12 :=
  center_cyclic_dvd_of_bounds (isPresentation_m22Gen h hbd) m22Comm
    (lift_m22CommWord h) (lift_m22B11 h) hcov (by rw [card_M22]) hQ e

end CFSG.Sporadic.Recognition.M22Multiplier
