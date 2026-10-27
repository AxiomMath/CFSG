module

public import CFSG.Timmesfeld.ARS.QDBasic

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

@[expose] def restrict (R : Set (Subgroup G)) (H : Subgroup G) : Set (Subgroup H) :=
  (fun B : Subgroup G => B.subgroupOf H) '' {B | B ∈ R ∧ B ≤ H}

namespace Restrict

variable {H : Subgroup G}

theorem commuting_subgroupOf_iff {B C : Subgroup G} :
    Commuting (B.subgroupOf H) (C.subgroupOf H) ↔ Commuting (B ⊓ H) (C ⊓ H) := by
  constructor
  · intro h b hb c hc
    have := h ⟨b, hb.2⟩ hb.1 ⟨c, hc.2⟩ hc.1
    exact congrArg Subtype.val this
  · intro h b hb c hc
    exact Subtype.ext (h b ⟨hb, b.2⟩ c ⟨hc, c.2⟩)

theorem commutator_subgroupOf {B C : Subgroup G} (hB : B ≤ H) (hC : C ≤ H) :
    ⁅B.subgroupOf H, C.subgroupOf H⁆ = (⁅B, C⁆ : Subgroup G).subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hB,
    Subgroup.map_subgroupOf_eq_of_le hC,
    Subgroup.map_subgroupOf_eq_of_le (QD.commutator_le_of_le hB hC)]

theorem opposite_subgroupOf {B C : Subgroup G} (hB : B ≤ H) (hC : C ≤ H) (h : Opposite B C) :
    Opposite (B.subgroupOf H) (C.subgroupOf H) := by
  refine ⟨fun e => h.1 ((subgroupOf_inj_of_le hB hC).1 e), ?_, ?_⟩
  · intro a ha ha1
    obtain ⟨b, hb, hb1, hab⟩ := h.2.1 a ha (fun e => ha1 (Subtype.ext e))
    refine ⟨⟨b, hC hb⟩, hb, fun e => hb1 (congrArg Subtype.val e), ?_⟩
    change (B.subgroupOf H).map (MulAut.conj (⟨b, hC hb⟩ : H)).toMonoidHom =
      (C.subgroupOf H).map (MulAut.conj (⟨(a : G), a.2⟩ : H)).toMonoidHom
    rw [map_conj_subgroupOf_mk, map_conj_subgroupOf_mk, hab]
  · intro c hc hc1
    obtain ⟨a, ha, ha1, hca⟩ := h.2.2 c hc (fun e => hc1 (Subtype.ext e))
    refine ⟨⟨a, hB ha⟩, ha, fun e => ha1 (congrArg Subtype.val e), ?_⟩
    change (C.subgroupOf H).map (MulAut.conj (⟨a, hB ha⟩ : H)).toMonoidHom =
      (B.subgroupOf H).map (MulAut.conj (⟨(c : G), c.2⟩ : H)).toMonoidHom
    rw [map_conj_subgroupOf_mk, map_conj_subgroupOf_mk, hca]

end Restrict

open Restrict

theorem isRootClass_restrict (hR : IsRootClass R) {H E₀ : Subgroup G} (hE₀ : E₀ ∈ R)
    (hE₀H : E₀ ≤ H) (hconj : ∀ B ∈ R, B ≤ H → ∃ g ∈ H, conjSub E₀ g = B)
    (hgen : H ≤ ⨆ B ∈ {B | B ∈ R ∧ B ≤ H}, B) : IsRootClass (restrict R H) := by
  refine ⟨⟨E₀.subgroupOf H, Set.Subset.antisymm ?_ ?_⟩, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨B, ⟨hB, hBH⟩, rfl⟩
    obtain ⟨g, hg, rfl⟩ := hconj B hB hBH
    exact ⟨⟨g, hg⟩, map_conj_subgroupOf_mk hg⟩
  · rintro _ ⟨g, rfl⟩
    exact ⟨conjSub E₀ g, ⟨hR.conjSub_mem hE₀ g, conjSub_le hE₀H g.2⟩,
      (map_conj_subgroupOf_mk g.2).symm⟩
  · rintro _ ⟨B, ⟨hB, hBH⟩, rfl⟩ hbot
    rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_of_le_left hBH] at hbot
    exact hR.ne_bot B hB hbot
  · rintro _ ⟨B, ⟨hB, -⟩, rfl⟩ a ha
    exact Subtype.ext (hR.mul_self B hB a ha)
  · rintro _ ⟨B, ⟨hB, hBH⟩, rfl⟩ _ ⟨C, ⟨hC, hCH⟩, rfl⟩ hne
    have hBC : B ≠ C := fun e => hne (e ▸ rfl)
    rcases hR.rel B hB C hC hBC with hc | ho | hs
    · left
      rw [commuting_subgroupOf_iff, inf_of_le_left hBH, inf_of_le_left hCH]
      exact hc
    · exact Or.inr (Or.inl (opposite_subgroupOf hBH hCH ho))
    · right; right
      have hTH : ⁅B, C⁆ ≤ H := QD.commutator_le_of_le hBH hCH
      rw [Special, commutator_subgroupOf hBH hCH, commuting_subgroupOf_iff,
        commuting_subgroupOf_iff, inf_of_le_left hBH, inf_of_le_left hCH, inf_of_le_left hTH]
      exact ⟨⟨_, ⟨hs.1, hTH⟩, rfl⟩, hs.2.1, hs.2.2⟩
  · refine eq_top_iff.2 fun x _ => ?_
    have hx : (x : G) ∈ ⨆ B ∈ {B | B ∈ R ∧ B ≤ H}, B := hgen x.2
    obtain ⟨hxH, hmem⟩ := gen_induction (Δ := {B | B ∈ R ∧ B ≤ H})
      (p := fun y => ∃ hy : y ∈ H, (⟨y, hy⟩ : H) ∈ ⨆ X ∈ restrict R H, X) hx
      (fun B hB z hz => ⟨hB.2 hz, le_iSup₂ (f := fun (X : Subgroup H) (_ : X ∈ restrict R H) => X)
        (B.subgroupOf H) ⟨B, hB, rfl⟩ (show (⟨z, hB.2 hz⟩ : H) ∈ B.subgroupOf H from hz)⟩)
      ⟨H.one_mem, Subgroup.one_mem _⟩ fun y z ⟨hyH, hy⟩ ⟨hzH, hz⟩ =>
        ⟨H.mul_mem hyH hzH, Subgroup.mul_mem _ hy hz⟩
    exact hmem

theorem noIsolated_restrict {H : Subgroup G}
    (h : ∀ B ∈ R, B ≤ H → ∃ C ∈ R, C ≤ H ∧ Opposite B C) : NoIsolated (restrict R H) := by
  rintro _ ⟨B, ⟨hB, hBH⟩, rfl⟩
  obtain ⟨C, hC, hCH, hBC⟩ := h B hB hBH
  exact ⟨C.subgroupOf H, ⟨C, ⟨hC, hCH⟩, rfl⟩, opposite_subgroupOf hBH hCH hBC⟩

end CFSG.Timmesfeld.ARS
