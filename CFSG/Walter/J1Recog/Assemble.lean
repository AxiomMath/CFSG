module

public import CFSG.Walter.J1Recog.Cert
public import CFSG.Walter.J1Recog.Vals

public section

namespace CFSG.Walter.J1Recog

open Word

theorem relVals_eq_one {c : Case} {G : Type*} [Group G] {f : Fin 5 → G}
    (hf : ∀ w ∈ rels c, ev f w = 1) : ∀ x ∈ relVals c (f 0) (f 1) (f 2) (f 3) (f 4), x = 1 :=
  (forall_ev_rels_iff c f).mp hf

theorem hVals_eq_one {c : Case} {G : Type*} [Group G] {f : Fin 5 → G}
    (hf : ∀ w ∈ rels c, ev f w = 1) : ∀ x ∈ hVals (f 0) (f 1) (f 2), x = 1 := fun x hx =>
  relVals_eq_one hf x (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hx)))

theorem presH_rels : ∀ w ∈ hRels, ev (fun i : Fin 3 =>
    (PresentedGroup.of (Fin.castLE (by norm_num) i) : Pres .O1a)) w = 1 := by
  intro w hw
  have h1 := List.mem_map_of_mem (f := ev (fun i : Fin 3 =>
    (PresentedGroup.of (Fin.castLE (by norm_num) i) : Pres .O1a))) hw
  rw [map_ev_hRels] at h1
  exact hVals_eq_one (c := .O1a) (f := PresentedGroup.of) (fun _ hw => ev_of_mem hw) _ h1

noncomputable def presHHom : PresH →* Pres .O1a :=
  lift hRels _ presH_rels

theorem tnm_le_range : tnm .O1a ≤ presHHom.range := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl | rfl)
  · exact ⟨PresentedGroup.of 0, lift_of _ _ _ 0⟩
  · exact ⟨PresentedGroup.of 1, lift_of _ _ _ 1⟩
  · exact ⟨PresentedGroup.of 2, lift_of _ _ _ 2⟩

theorem card_tnm_le : Finite (tnm .O1a) ∧ Nat.card (tnm .O1a) ≤ 168 := by
  obtain ⟨hfin, hcard⟩ := card_presH_le
  have hle : Nat.card presHHom.range ≤ Nat.card PresH :=
    Nat.card_le_card_of_surjective _ presHHom.rangeRestrict_surjective
  have : Finite presHHom.range := Finite.of_surjective _ presHHom.rangeRestrict_surjective
  have hfin' : Finite (tnm .O1a) := Finite.of_injective _ (Subgroup.inclusion_injective
    tnm_le_range)
  exact ⟨hfin', (Subgroup.card_le_of_le tnm_le_range).trans (hle.trans hcard)⟩

theorem finite_card_le : Finite (Pres .O1a) ∧ Nat.card (Pres .O1a) ≤ 175560 := by
  obtain ⟨hfi, hidx⟩ := index_le_O1a
  obtain ⟨hfin, hcard⟩ := card_tnm_le
  have h := (tnm .O1a).card_mul_index
  have hpos : 0 < Nat.card (tnm .O1a) := Nat.card_pos
  have hne : Nat.card (Pres .O1a) ≠ 0 := by
    rw [← h]
    exact Nat.mul_ne_zero hpos.ne' hfi.index_ne_zero
  refine ⟨Nat.finite_of_card_ne_zero hne, ?_⟩
  rw [← h]
  calc Nat.card (tnm .O1a) * (tnm .O1a).index ≤ 168 * 1045 := Nat.mul_le_mul hcard hidx
    _ = 175560 := by norm_num

end CFSG.Walter.J1Recog
