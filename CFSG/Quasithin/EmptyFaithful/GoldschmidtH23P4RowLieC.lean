module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4RowLieA
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4OutAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Lattice

public section

namespace CFSG.Quasithin.H23P4

open Equiv CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L.Seven

theorem dGens_sign : ∀ g ∈ dGens, Perm.sign g = 1 := by
  intro g hg
  simp only [dGens, perm7, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;>
    simp [List.formPerm_cons_cons, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap']

theorem D7_le_alternating : D7 ≤ alternatingGroup (Fin 7) := by
  rw [D7, Subgroup.closure_le]
  intro g hg
  exact Equiv.Perm.mem_alternatingGroup.mpr (dGens_sign g hg)

theorem card_alternating_seven : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

section Lattice


theorem card_lat_a7 {i : ℕ} (hi : i < 12) :
    Nat.card (Z i) = [8, 24, 24, 24, 24, 24, 72, 120, 168, 168, 360, 2520].getD i 0 := by
  have hG : latGens.getD i [] ∈ latGens := by
    rw [List.getD_eq_getElem _ _ (by simpa [latGens] using hi)]
    exact List.getElem_mem _
  rw [Z, card_closure_of_closedH rawIsEnc7 _ depth (List.all_eq_true.mp closed_lat _ hG)]
  have hi' : i < latGens.length := by simpa [latGens] using hi
  have h2 : (latGens.map (fun G => (elts G).size)).getD i 0 = (elts (latGens.getD i [])).size := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getD_eq_getElem _ _ hi',
      List.getElem_map]
  show (elts (latGens.getD i [])).size = _
  rw [← h2, sizes_lat]

theorem card_D7_a7 : Nat.card D7 = 8 := by
  have := card_lat_a7 (i := 0) (by norm_num)
  simpa [Z, D7, latGens] using this

theorem card_D7_subgroupOf : Nat.card (D7.subgroupOf (alternatingGroup (Fin 7))) = 8 :=
  (Nat.card_congr (Subgroup.subgroupOfEquivOfLe D7_le_alternating).toEquiv).trans card_D7_a7

theorem isSylowTwoOf_D7 : IsSylowTwoOf (D7.subgroupOf (alternatingGroup (Fin 7))) ⊤ := by
  have hmul := Subgroup.card_mul_index (D7.subgroupOf (alternatingGroup (Fin 7)))
  rw [card_D7_subgroupOf, card_alternating_seven] at hmul
  have hi : (D7.subgroupOf (alternatingGroup (Fin 7))).index = 315 := by omega
  rw [isSylowTwoOf_top_iff, hi]
  exact ⟨IsPGroup.of_card (n := 3) (by rw [card_D7_subgroupOf]; norm_num), by norm_num⟩

theorem card_overgroup_a7 (U : Subgroup ↥(alternatingGroup (Fin 7)))
    (hU : D7.subgroupOf (alternatingGroup (Fin 7)) ≤ U) :
    Nat.card U ∈ [8, 24, 72, 120, 168, 360, 2520] := by
  have hinj : Function.Injective (alternatingGroup (Fin 7)).subtype :=
    (alternatingGroup (Fin 7)).subtype_injective
  have hD : D7 ≤ U.map (alternatingGroup (Fin 7)).subtype := fun d hd =>
    ⟨⟨d, D7_le_alternating hd⟩, hU (by rwa [Subgroup.mem_subgroupOf]), rfl⟩
  have hev : ∀ y ∈ U.map (alternatingGroup (Fin 7)).subtype, Perm.sign y = 1 := by
    rintro _ ⟨y, -, rfl⟩
    exact Equiv.Perm.mem_alternatingGroup.mp y.2
  obtain ⟨i, hi, hY⟩ := overgroups_A7 hD hev
  rw [← Subgroup.card_map_of_injective hinj, hY, card_lat_a7 hi]
  interval_cases i <;> simp

theorem noFiveIndex_alternating_seven : NoFiveIndex (alternatingGroup (Fin 7)) :=
  NoFiveIndex.of_card_overgroups isSylowTwoOf_D7 card_D7_subgroupOf (by norm_num)
    [8, 24, 72, 120, 168, 360, 2520] card_overgroup_a7 (by decide) (by decide)

theorem rowOK_alternating_seven : RowOK (alternatingGroup (Fin 7)) where
  center := alternatingGroup.center_eq_bot (by simp)
  out := CFSG.Quasithin.H23Out.out5Pow_alternating (by norm_num)
  idx := noFiveIndex_alternating_seven

end Lattice

end CFSG.Quasithin.H23P4
