module

public import CFSG.Quasithin.Recognition.L34AmalgamHom
public import Certificates.Certificate7078

public section

namespace CFSG.Quasithin.L34Amalgam

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94 CFSG.CosetTable

theorem cert_relsP1 : subsetCheck relsP1 [] 100000 960 = true :=
  Certificates.certificate7078.1

theorem cert_relsP2 : subsetCheck relsP2 [] 100000 960 = true :=
  Certificates.certificate7078.2

theorem word_u : word "u" = [(4, true)] := by decide

theorem gen₁_four : gen₁ 4 = 1 := by
  rw [gen₁, dite_eq_left rfl]

theorem gen₂_three : gen₂ 3 = 1 := by
  rw [gen₂, dite_eq_left rfl]

theorem gen₁_relsP1 : ∀ w ∈ relsP1, evalW gen₁ w = 1 := by
  intro w hw
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hw
  rcases List.mem_append.mp hs with hs | hs
  · apply Subtype.ext
    rw [coe_evalW_gen₁ (letters_ne_four hs), Subgroup.coe_one]
    exact evalW_amalRels _ (List.mem_map.mpr ⟨s, List.mem_append_left _ hs, rfl⟩)
  · rw [List.mem_singleton.mp hs, word_u]
    simp [evalW, gen₁_four]

theorem gen₂_relsP2 : ∀ w ∈ relsP2, evalW gen₂ w = 1 := by
  intro w hw
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hw
  rcases List.mem_append.mp hs with hs | hs
  · apply Subtype.ext
    rw [coe_evalW_gen₂ (letters_ne_three hs), Subgroup.coe_one]
    exact evalW_amalRels _ (List.mem_map.mpr ⟨s, List.mem_append_right _ hs, rfl⟩)
  · rw [List.mem_singleton.mp hs, word_s]
    simp [evalW, gen₂_three]

theorem lift_eq_one_of {X : Type*} [Group X] {f : Fin 5 → X} {ws : List (List (Fin 5 × Bool))}
    (hf : ∀ w ∈ ws, evalW f w = 1) :
    ∀ r ∈ {r : FreeGroup (Fin 5) | r ∈ ws.map FreeGroup.mk}, FreeGroup.lift f r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
  rw [← evalW_eq_lift]
  exact hf w hw

@[expose] noncomputable def presHom {X : Type*} [Group X] (ws : List (List (Fin 5 × Bool)))
    (f : Fin 5 → X) (hf : ∀ w ∈ ws, evalW f w = 1) : PG 5 ws →* X :=
  PresentedGroup.toGroup (lift_eq_one_of hf)

theorem presHom_of {X : Type*} [Group X] (ws : List (List (Fin 5 × Bool))) (f : Fin 5 → X)
    (hf : ∀ w ∈ ws, evalW f w = 1) (j : Fin 5) : presHom ws f hf (PresentedGroup.of j) = f j :=
  PresentedGroup.toGroup.of _

theorem presHom_surj₁ :
    Function.Surjective (presHom relsP1 gen₁ gen₁_relsP1) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_gen₁, Subgroup.closure_le]
  rintro _ ⟨j, -, rfl⟩
  exact ⟨PresentedGroup.of j, presHom_of _ _ _ j⟩

theorem presHom_surj₂ :
    Function.Surjective (presHom relsP2 gen₂ gen₂_relsP2) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_gen₂, Subgroup.closure_le]
  rintro _ ⟨j, -, rfl⟩
  exact ⟨PresentedGroup.of j, presHom_of _ _ _ j⟩

@[expose] noncomputable def pres1 :
    PG 5 relsP1 ≃* ↥m22TwoStab :=
  have : Finite (PG 5 relsP1) := (card_le_of_subsetCheck_nil _ cert_relsP1).1
  MulEquiv.ofBijective (presHom relsP1 gen₁ gen₁_relsP1) (presHom_surj₁.bijective_of_nat_card_le
    (by rw [card_m22TwoStab]; exact (card_le_of_subsetCheck_nil _ cert_relsP1).2))

@[expose] noncomputable def pres2 :
    PG 5 relsP2 ≃* ↥m22PtHexStab :=
  have : Finite (PG 5 relsP2) := (card_le_of_subsetCheck_nil _ cert_relsP2).1
  MulEquiv.ofBijective (presHom relsP2 gen₂ gen₂_relsP2) (presHom_surj₂.bijective_of_nat_card_le
    (by rw [M22Witt.card_m22PtHexStab]; exact (card_le_of_subsetCheck_nil _ cert_relsP2).2))

theorem pres1_of
    (j : Fin 5) : pres1 (PresentedGroup.of j) = gen₁ j :=
  presHom_of relsP1 gen₁ gen₁_relsP1 j

theorem pres2_of
    (j : Fin 5) : pres2 (PresentedGroup.of j) = gen₂ j :=
  presHom_of relsP2 gen₂ gen₂_relsP2 j

@[expose] noncomputable def endo1
    (f : Fin 5 → ↥m22TwoStab) (hf : ∀ w ∈ relsP1, evalW f w = 1) :
    ↥m22TwoStab →* ↥m22TwoStab :=
  (presHom relsP1 f hf).comp pres1.symm.toMonoidHom

@[expose] noncomputable def endo2
    (f : Fin 5 → ↥m22PtHexStab)
    (hf : ∀ w ∈ relsP2, evalW f w = 1) : ↥m22PtHexStab →* ↥m22PtHexStab :=
  (presHom relsP2 f hf).comp pres2.symm.toMonoidHom

theorem endo1_gen
    (f : Fin 5 → ↥m22TwoStab) (hf : ∀ w ∈ relsP1, evalW f w = 1) (j : Fin 5) :
    endo1 f hf (gen₁ j) = f j := by
  have e : pres1.symm (gen₁ j) = PresentedGroup.of j := by
    rw [MulEquiv.symm_apply_eq, pres1_of]
  rw [endo1, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e, presHom_of]

theorem endo2_gen
    (f : Fin 5 → ↥m22PtHexStab) (hf : ∀ w ∈ relsP2, evalW f w = 1)
    (j : Fin 5) :
    endo2 f hf (gen₂ j) = f j := by
  have e : pres2.symm (gen₂ j) = PresentedGroup.of j := by
    rw [MulEquiv.symm_apply_eq, pres2_of]
  rw [endo2, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e, presHom_of]

abbrev bB1 : Subgroup ↥m22TwoStab := m22PtHexStab.subgroupOf m22TwoStab

abbrev bB2 : Subgroup ↥m22PtHexStab := m22TwoStab.subgroupOf m22PtHexStab

theorem card_bB1 :
    Nat.card bB1 = 192 := by
  show Nat.card (m22PtHexStab.subgroupOf m22TwoStab) = 192
  rw [← Subgroup.inf_subgroupOf_left,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, card_B]

theorem card_bB2 :
    Nat.card bB2 = 192 := by
  show Nat.card (m22TwoStab.subgroupOf m22PtHexStab) = 192
  rw [← Subgroup.inf_subgroupOf_left,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, inf_comm, card_B]

theorem bijective_of_map_B1
    {α : ↥m22TwoStab →* ↥m22TwoStab} (hB : bB1.map α = bB1)
    {x : ↥m22TwoStab} (hx : α x ∉ bB1) : Function.Bijective α := by
  have hle : bB1 ≤ α.range := by
    rw [← hB]
    exact Subgroup.map_le_range α bB1
  have htop : α.range = ⊤ := eq_of_card_eq_five_mul hle le_top
    (by rw [Subgroup.card_top, card_m22TwoStab, card_bB1]) ⟨x, rfl⟩ hx
  have hs : Function.Surjective α := MonoidHom.range_eq_top.mp htop
  exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩

theorem bijective_of_map_B2
    {α : ↥m22PtHexStab →* ↥m22PtHexStab} (hB : bB2.map α = bB2)
    {x : ↥m22PtHexStab} (hx : α x ∉ bB2) : Function.Bijective α := by
  have hle : bB2 ≤ α.range := by
    rw [← hB]
    exact Subgroup.map_le_range α bB2
  have htop : α.range = ⊤ := eq_of_card_eq_five_mul hle le_top
    (by rw [Subgroup.card_top, M22Witt.card_m22PtHexStab, card_bB2]) ⟨x, rfl⟩ hx
  have hs : Function.Surjective α := MonoidHom.range_eq_top.mp htop
  exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩

end CFSG.Quasithin.L34Amalgam
