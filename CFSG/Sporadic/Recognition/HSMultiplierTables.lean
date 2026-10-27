module

public import CFSG.Sporadic.Recognition.HSMultiplierInputs
public import CFSG.Sporadic.Bridge.HSSurj

public section

namespace CFSG.Sporadic.Recognition.HSMultiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Bridge.TwoGen.Native CFSG.Sporadic.Recognition.CoverTransfer
  CFSG.Sporadic.Recognition.CoverRecipe CFSG.Sporadic.SmallF2 CFSG.Sporadic.Th
open CFSG.Sporadic.HS.Native (hsData)

@[expose] noncomputable def hsAb (i : Fin 2) : J hsData := img2 (a hsData) (b hsData) i.val

@[expose] noncomputable def hsGen (i : Fin 6) : J hsData :=
  FreeGroup.lift hsAb (FreeGroup.mk (hsGenWords.getD i []))

section Tables


theorem lift_hsAb_eq_one (h : hsTabCheck = true) {w : List (Fin 2 × Bool)}
    (hw : w ∈ hsCheckWords) : FreeGroup.lift hsAb (FreeGroup.mk w) = 1 := by
  have := faithful CFSG.Sporadic.Bridge.HS.baseFacts
  have hA := rep_a CFSG.Sporadic.Bridge.HS.baseFacts
  have hB := rep_b CFSG.Sporadic.Bridge.HS.baseFacts
  exact lift_eq_one_of_relCheck (n := hsData.n) (n_lt_two_pow CFSG.Sporadic.HS.hsFacts) hA
    (Rep.inv_of_invOK hA CFSG.Sporadic.Bridge.HS.baseFacts.invA) hB
    (Rep.inv_of_invOK hB CFSG.Sporadic.Bridge.HS.baseFacts.invB) h hw

theorem lift_hsAb_eq_of_inv_mem (h : hsTabCheck = true) {u : List (Fin 2 × Bool)} {i : Fin 2}
    (hu : u ++ [(i, false)] ∈ hsCheckWords) :
    FreeGroup.lift hsAb (FreeGroup.mk u) = hsAb i := by
  have := faithful CFSG.Sporadic.Bridge.HS.baseFacts
  have hA := rep_a CFSG.Sporadic.Bridge.HS.baseFacts
  have hB := rep_b CFSG.Sporadic.Bridge.HS.baseFacts
  exact lift_eq_of_inv_mem (n := hsData.n) (n_lt_two_pow CFSG.Sporadic.HS.hsFacts) hA
    (Rep.inv_of_invOK hA CFSG.Sporadic.Bridge.HS.baseFacts.invA) hB
    (Rep.inv_of_invOK hB CFSG.Sporadic.Bridge.HS.baseFacts.invB) h hu

end Tables

theorem lift_hsGen_mk (r : List (Fin 6 × Bool)) :
    FreeGroup.lift hsGen (FreeGroup.mk r) =
      FreeGroup.lift hsAb (FreeGroup.mk (substWord hsGenWords r)) :=
  lift_mk_substWord hsAb hsGenWords r

theorem substWord_rel_mem {r : List (Fin 6 × Bool)} (hr : r ∈ hsRels) :
    substWord hsGenWords r ∈ hsCheckWords := by
  unfold hsCheckWords
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hr))

theorem substWord_comm_mem (i : Fin 6) :
    substWord hsGenWords ((i, false) :: hsCommWord i) ∈ hsCheckWords := by
  unfold hsCheckWords
  exact List.mem_append_left _
    (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩))

section Relators


theorem lift_hsGen_rels (h : hsTabCheck = true) :
    ∀ r ∈ wordSet hsRels, FreeGroup.lift hsGen r = 1 := by
  intro r hr
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hr
  rw [lift_hsGen_mk]
  exact lift_hsAb_eq_one h (substWord_rel_mem hv)

theorem lift_hsCommWord (h : hsTabCheck = true) (i : Fin 6) :
    FreeGroup.lift hsGen (FreeGroup.mk (hsCommWord i)) = hsGen i := by
  have h1 : FreeGroup.lift hsGen (FreeGroup.mk ((i, false) :: hsCommWord i)) = 1 := by
    rw [lift_hsGen_mk]
    exact lift_hsAb_eq_one h (substWord_comm_mem i)
  rw [show FreeGroup.mk ((i, false) :: hsCommWord i) =
      (FreeGroup.of i)⁻¹ * FreeGroup.mk (hsCommWord i) from rfl, map_mul, map_inv,
    FreeGroup.lift_apply_of, inv_mul_eq_one] at h1
  exact h1.symm

theorem closure_hsGen (h : hsTabCheck = true) : Subgroup.closure (Set.range hsGen) = ⊤ := by
  refine closure_range_eq_top (closure_ab hsData) (sA := hsSurjA) (sB := hsSurjB) ?_ ?_
  · rw [lift_hsGen_mk]
    exact (lift_hsAb_eq_of_inv_mem h (u := substWord hsGenWords hsSurjA) (i := 0) (by
      unfold hsCheckWords
      exact List.mem_append_right _ List.mem_cons_self)).symm
  · rw [lift_hsGen_mk]
    exact (lift_hsAb_eq_of_inv_mem h (u := substWord hsGenWords hsSurjB) (i := 1) (by
      unfold hsCheckWords
      exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))).symm

theorem card_J : Nat.card (J hsData) = 44352000 := by
  rw [← Nat.card_congr CFSG.Sporadic.Bridge.HS.nativeEquiv.toEquiv, CFSG.Sporadic.HS.card_HS]

end Relators

end CFSG.Sporadic.Recognition.HSMultiplier
