module

public import CFSG.RankThree.PartTwo.Sec21.FF81F4L3

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
  CFSG.RankThree.PartTwo.Sec21.FF79.L41 CFSG.RankThree.PartTwo.Sec21.FF81
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

section Transfer

variable {X : Type} [Group X] {Y : Subgroup X}

theorem orderOf_e (e : ↥Y ≃* F42C) {u : X} (hu : u ∈ Y) : orderOf (e ⟨u, hu⟩) = orderOf u := by
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]

theorem mem_of_nor {g : X} (hg : g ∈ Nor Y) {u : X} (hu : u ∈ Y) : g * u * g⁻¹ ∈ Y :=
  ((Subgroup.mem_normalizer_iff.1 hg) u).1 hu

theorem indAut_e (e : ↥Y ≃* F42C) {g : X} (hg : g ∈ Nor Y) {u : X} (hu : u ∈ Y) :
    indAut e hg (e ⟨u, hu⟩) = e ⟨g * u * g⁻¹, mem_of_nor hg hu⟩ := by
  apply e.symm.injective
  apply Subtype.ext
  rw [indAut_apply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

end Transfer

section Clauses


variable {X : Type} [Group X] {Y : Subgroup X}

theorem clause_outer_two (e : ↥Y ≃* F42C) {g : X} (hg : g ∈ Nor Y)
    (hout : ¬ ∃ y ∈ Y, ∀ x ∈ Y, g * x * g⁻¹ = y * x * y⁻¹) :
    ∀ u ∈ Y, ∀ v ∈ Y, orderOf u = 2 → orderOf v = 2 →
      Nat.card ↥(Y ⊓ Cen u) = 2 ^ 24 * 3 ^ 4 * 5 * 7 →
      Nat.card ↥(Y ⊓ Cen v) = 2 ^ 24 * 3 ^ 4 * 5 * 7 →
      ∃ y ∈ Y, y * u * y⁻¹ = v ∨ y * (g * u * g⁻¹) * y⁻¹ = v := by
  intro u hu v hv hu2 hv2 hcu hcv
  have hαo := (indAut_not_inner_iff e hg).2 hout
  rw [card_inf_cen e hu] at hcu
  rw [card_inf_cen e hv] at hcv
  have hu2' : orderOf (e ⟨u, hu⟩) = 2 := by rw [orderOf_e e hu]; exact hu2
  have hv2' : orderOf (e ⟨v, hv⟩) = 2 := by rw [orderOf_e e hv]; exact hv2
  rcases L1b_C (indAut e hg) hαo hu2' hv2' hcu hcv with ⟨c, hc⟩ | ⟨c, hc⟩
  · obtain ⟨y, hy, h⟩ := (exists_conj_iff e hu hv).2 ⟨c, hc⟩
    exact ⟨y, hy, Or.inl h⟩
  · rw [indAut_e e hg hu] at hc
    obtain ⟨y, hy, h⟩ := (exists_conj_iff e (mem_of_nor hg hu) hv).2 ⟨c, hc⟩
    exact ⟨y, hy, Or.inr h⟩

theorem clause_Syl2 [Finite X] (e : ↥Y ≃* F42C) :
    ∀ U : Subgroup X, IsSylowOf 2 U Y → Nat.card ↥(Subgroup.center ↥U) = 4 ∧
      U = Subgroup.closure {u | u ∈ U ∧ orderOf u = 2 ∧
        Nat.card ↥(Y ⊓ Cen u) = 2 ^ 24 * 3 ^ 4 * 5 * 7} := by
  intro U hU
  have hUY : U ≤ Y := hU.1
  have hcard : Nat.card ↥(toC e U) = 2 ^ 24 := (card_toC e hUY).trans (card_sylow_two e hU)
  obtain ⟨h1, h2⟩ := L3_C hcard
  have hmap := map_toC e hUY
  refine ⟨?_, ?_⟩
  · have e2 : ↥(toC e U) ≃* ↥U :=
      (Subgroup.equivMapOfInjective (toC e U) (ιY e) (ιY_injective e)).trans
        (MulEquiv.subgroupCongr hmap)
    rw [card_center_congr e2]
    exact h1
  · apply le_antisymm
    · intro x hx
      rw [← hmap] at hx
      obtain ⟨c, hc, rfl⟩ := hx
      have hc2 := (le_of_eq h2) hc
      have hmem : ιY e c ∈ (Subgroup.closure {u | u ∈ toC e U ∧ orderOf u = 2 ∧
          Nat.card ↥(Subgroup.centralizer ({u} : Set F42C)) = cenRoot}).map (ιY e) := ⟨c, hc2, rfl⟩
      rw [MonoidHom.map_closure] at hmem
      refine (Subgroup.closure_mono ?_) hmem
      rintro _ ⟨c', ⟨hc'U, hc'2, hc'cen⟩, rfl⟩
      refine ⟨hc'U, ?_, ?_⟩
      · rw [orderOf_injective (ιY e) (ιY_injective e), hc'2]
      · have h := map_cen_ιY e c'
        rw [← h, Subgroup.card_map_of_injective (ιY_injective e)]
        exact hc'cen
    · refine (Subgroup.closure_le U).2 fun u hu => hu.1

end Clauses

end CFSG.RankThree.PartTwo.Sec21.FF81.F4
