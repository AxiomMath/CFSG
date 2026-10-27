module

public import CFSG.Sporadic.Recognition.Co2MultiplierInputs
public import CFSG.Sporadic.Bridge.Co2Surj

public section

namespace CFSG.Sporadic.Recognition.Co2Multiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Bridge.TwoGen.Native CFSG.Sporadic.Recognition.CoverTransfer
  CFSG.Sporadic.Recognition.CoverRecipe CFSG.Sporadic.SmallF2 CFSG.Sporadic.Th
open CFSG.Sporadic.Co2.Native (co2Data)

@[expose] noncomputable def co2Ab (i : Fin 2) : J co2Data := img2 (a co2Data) (b co2Data) i.val

@[expose] noncomputable def co2Gen (i : Fin 7) : J co2Data :=
  FreeGroup.lift co2Ab (FreeGroup.mk (co2GenWords.getD i []))

section Tables


theorem lift_co2Ab_eq_one (h : co2TabCheck = true) {w : List (Fin 2 × Bool)}
    (hw : w ∈ co2CheckWords) : FreeGroup.lift co2Ab (FreeGroup.mk w) = 1 := by
  have := faithful CFSG.Sporadic.Bridge.Co2.baseFacts
  have hA := rep_a CFSG.Sporadic.Bridge.Co2.baseFacts
  have hB := rep_b CFSG.Sporadic.Bridge.Co2.baseFacts
  exact lift_eq_one_of_relCheck (n := co2Data.n) (n_lt_two_pow CFSG.Sporadic.Co2.co2Facts) hA
    (Rep.inv_of_invOK hA CFSG.Sporadic.Bridge.Co2.baseFacts.invA) hB
    (Rep.inv_of_invOK hB CFSG.Sporadic.Bridge.Co2.baseFacts.invB) h hw

theorem lift_co2Ab_eq_of_inv_mem (h : co2TabCheck = true) {u : List (Fin 2 × Bool)} {i : Fin 2}
    (hu : u ++ [(i, false)] ∈ co2CheckWords) :
    FreeGroup.lift co2Ab (FreeGroup.mk u) = co2Ab i := by
  have := faithful CFSG.Sporadic.Bridge.Co2.baseFacts
  have hA := rep_a CFSG.Sporadic.Bridge.Co2.baseFacts
  have hB := rep_b CFSG.Sporadic.Bridge.Co2.baseFacts
  exact lift_eq_of_inv_mem (n := co2Data.n) (n_lt_two_pow CFSG.Sporadic.Co2.co2Facts) hA
    (Rep.inv_of_invOK hA CFSG.Sporadic.Bridge.Co2.baseFacts.invA) hB
    (Rep.inv_of_invOK hB CFSG.Sporadic.Bridge.Co2.baseFacts.invB) h hu

end Tables

theorem lift_co2Gen_mk (r : List (Fin 7 × Bool)) :
    FreeGroup.lift co2Gen (FreeGroup.mk r) =
      FreeGroup.lift co2Ab (FreeGroup.mk (substWord co2GenWords r)) :=
  lift_mk_substWord co2Ab co2GenWords r

theorem substWord_rel_mem {r : List (Fin 7 × Bool)} (hr : r ∈ co2Rels) :
    substWord co2GenWords r ∈ co2CheckWords := by
  unfold co2CheckWords
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hr))

theorem substWord_comm_mem (i : Fin 7) :
    substWord co2GenWords ((i, false) :: co2CommWord i) ∈ co2CheckWords := by
  unfold co2CheckWords
  exact List.mem_append_left _
    (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩))

section Relators


theorem lift_co2Gen_rels (h : co2TabCheck = true) :
    ∀ r ∈ wordSet co2Rels, FreeGroup.lift co2Gen r = 1 := by
  intro r hr
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hr
  rw [lift_co2Gen_mk]
  exact lift_co2Ab_eq_one h (substWord_rel_mem hv)

theorem lift_co2CommWord (h : co2TabCheck = true) (i : Fin 7) :
    FreeGroup.lift co2Gen (FreeGroup.mk (co2CommWord i)) = co2Gen i := by
  have h1 : FreeGroup.lift co2Gen (FreeGroup.mk ((i, false) :: co2CommWord i)) = 1 := by
    rw [lift_co2Gen_mk]
    exact lift_co2Ab_eq_one h (substWord_comm_mem i)
  rw [show FreeGroup.mk ((i, false) :: co2CommWord i) =
      (FreeGroup.of i)⁻¹ * FreeGroup.mk (co2CommWord i) from rfl, map_mul, map_inv,
    FreeGroup.lift_apply_of, inv_mul_eq_one] at h1
  exact h1.symm

theorem closure_co2Gen (h : co2TabCheck = true) : Subgroup.closure (Set.range co2Gen) = ⊤ := by
  refine closure_range_eq_top (closure_ab co2Data) (sA := co2SurjA) (sB := co2SurjB) ?_ ?_
  · rw [lift_co2Gen_mk]
    exact (lift_co2Ab_eq_of_inv_mem h (u := substWord co2GenWords co2SurjA) (i := 0) (by
      unfold co2CheckWords
      exact List.mem_append_right _ List.mem_cons_self)).symm
  · rw [lift_co2Gen_mk]
    exact (lift_co2Ab_eq_of_inv_mem h (u := substWord co2GenWords co2SurjB) (i := 1) (by
      unfold co2CheckWords
      exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))).symm

theorem card_J : Nat.card (J co2Data) = 42305421312000 := by
  rw [← Nat.card_congr CFSG.Sporadic.Bridge.Co2.nativeEquiv.toEquiv, CFSG.Sporadic.Co2.card_Co2]

end Relators

end CFSG.Sporadic.Recognition.Co2Multiplier
