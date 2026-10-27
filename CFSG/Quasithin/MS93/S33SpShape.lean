module

public import CFSG.Quasithin.MS93.S33SpDich

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem relIndex_qv_zm_ne_one {A B : Type} {C : Type} [Group A] [Group C] [Group B]
    {X : GoldAmalgam A C B} {γ γ' : Vtx X} (hc : IsCritical X γ γ') :
    (Qv X γ').relIndex (ZM X γ) ≠ 1 := by
  rw [Ne, Subgroup.relIndex_eq_one]
  exact hc.2.2

section Shapes

variable {F : Type} [Field F] [Fintype F]

theorem shapes_at (h : PUHyp M T L) {α' μ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) (baseA _) α') (hμ : IsCritical (puAmalgam h.le) μ (baseA _))
    (hrel₁ : (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) =
      (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ μ))
    (hrel₂ : (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ α') =
      (Qv _ μ).relIndex (ZM (puAmalgam h.le) (baseA _)))
    {A₁ : Subgroup G} {α₁ : ↥A₁ →* ↥(StatedSp 2 F)} (hA₁M : A₁ ≤ M)
    (hnat₁ : IsSumOfNaturalModulesVia A₁ (Uq M T L) (Uq M T L ⊓ Zq M L) α₁ false 1)
    (hE₁ : pre h.le (ZM _ μ) ≤ A₁)
    {A₂ : Subgroup G} {α₂ : ↥A₂ →* ↥(StatedSp 2 F)} (hA₂M : A₂ ≤ M)
    (hnat₂ : IsSumOfNaturalModulesVia A₂ (Uq M T L) (Uq M T L ⊓ Zq M L) α₂ false 1)
    (hE₂ : pre h.le (ZM _ α') ≤ A₂) :
    ((∃ p : Submodule F (MSP.V4 F), MSP.IsPoint p ∧
          ((pre h.le (ZM _ μ)).subgroupOf A₁).map α₁ = MSP.xPoint p) ∧
        (∃ p' : Submodule F (MSP.V4 F), MSP.IsPoint p' ∧
          ((pre h.le (ZM _ α')).subgroupOf A₂).map α₂ = MSP.xPoint p') ∧
        (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) = Fintype.card F ∧
        (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ α') = Fintype.card F) ∨
      (Fintype.card F ^ 2 ≤ (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) ∧
        Fintype.card F ^ 2 ≤ (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ α') ∧
        Module.finrank F (MSP.fixSp (((pre h.le (ZM _ μ)).subgroupOf A₁).map α₁)) ≤ 2 ∧
        Module.finrank F (MSP.fixSp (((pre h.le (ZM _ α')).subgroupOf A₂).map α₂)) ≤ 2) := by
  have h20 := h.hyp20
  have hb := h.critDist_pos
  have hC := h.centHyp
  have hc' := ms22_iii _ h20 hb hC hc
  have hμ' := ms22_iii _ h20 hb hC hμ
  obtain ⟨c₁⟩ := MSP.nonempty_natCoord hnat₁
  obtain ⟨c₂⟩ := MSP.nonempty_natCoord hnat₂
  set Γ := ((pre h.le (ZM _ μ)).subgroupOf A₁).map α₁ with hΓ
  set Γ' := ((pre h.le (ZM _ α')).subgroupOf A₂).map α₂ with hΓ'
  have hcΓ : Nat.card Γ = (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) := by
    rw [hΓ, card_image_eq_relIndex h hA₁M c₁ hE₁, hrel₁, relIndex_qv_zm_eq h hμ]
  have hcΓ' : Nat.card Γ' = (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ α') := by
    rw [hΓ', card_image_eq_relIndex h hA₂M c₂ hE₂, relIndex_qv_zm_eq h hc']
  have h1 : Nat.card (MSP.V4 F) ≤ Nat.card (MSP.fixSp Γ') * Nat.card Γ := by
    refine (card_le_fixSp_mul h hA₂M c₂ (pre h.le (ZM _ α'))).trans
      (Nat.mul_le_mul_left _ ?_)
    rw [hcΓ]
    exact relIndex_centralizer_le h hc
  have h2 : Nat.card (MSP.V4 F) ≤ Nat.card (MSP.fixSp Γ) * Nat.card Γ' := by
    refine (card_le_fixSp_mul h hA₁M c₁ (pre h.le (ZM _ μ))).trans
      (Nat.mul_le_mul_left _ ?_)
    rw [hcΓ', hrel₂]
    exact relIndex_centralizer_le h hμ'
  have hΓ1 : Γ ≠ ⊥ := by
    intro hbot
    have := hcΓ
    rw [hbot, Subgroup.card_bot] at this
    exact relIndex_qv_zm_ne_one hc this.symm
  have hΓ'1 : Γ' ≠ ⊥ := by
    intro hbot
    have := hcΓ'
    rw [hbot, Subgroup.card_bot] at this
    exact relIndex_qv_zm_ne_one hc' this.symm
  rcases sp4_shapes hΓ1 hΓ'1 h1 h2 with ⟨⟨p, hp, hpe⟩, ⟨p', hp', hpe'⟩⟩ | ⟨hq1, hq2, hd1, hd2⟩
  · refine Or.inl ⟨⟨p, hp, hpe⟩, ⟨p', hp', hpe'⟩, ?_, ?_⟩
    · rw [← hcΓ, hpe, MSP.card_xPoint hp, Nat.card_eq_fintype_card]
    · rw [← hcΓ', hpe', MSP.card_xPoint hp', Nat.card_eq_fintype_card]
  · exact Or.inr ⟨hcΓ ▸ hq1, hcΓ' ▸ hq2, hd1, hd2⟩

theorem natural_data_of_sp (h : PUHyp M T L) {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hF : 4 ≤ Fintype.card F) {α : ↥L →* ↥(StatedSp 2 F)} (hα : Function.Surjective α)
    (hnat : IsSumOfNaturalModulesVia L (Uq M T L) (Uq M T L ⊓ Zq M L) α false 1)
    {γ : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) γ (baseA _)) :
    ∃ αγ : ↥(L ⊔ pre h.le (ZM _ γ)) →* ↥(StatedSp 2 F),
      IsSumOfNaturalModulesVia (L ⊔ pre h.le (ZM _ γ)) (Uq M T L) (Uq M T L ⊓ Zq M L) αγ
        false 1 := by
  obtain ⟨hLV, hCV, β, hβ, hβker, hβα⟩ := id hnat
  have hβα' := isCoordAct_of_natSp hβα
  have hT := exists_sp4_mat_of_isCritical h hα hβ hβker hβα' hcard hF hc
  obtain ⟨αγ, -, hnatγ⟩ := exists_natural_of_coordAct (Γ := StatedSp 2 F) rfl hα hLV hCV hβ hβker
    hβα ((pre_le h.le _).trans (le_normalizer_Uq h.le_normalizer)) hT
  exact ⟨αγ, hnatγ⟩

theorem shapes_of_sp (h : PUHyp M T L) {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (hF : 4 ≤ Fintype.card F) {α : ↥L →* ↥(StatedSp 2 F)} (hα : Function.Surjective α)
    (hnat : IsSumOfNaturalModulesVia L (Uq M T L) (Uq M T L ⊓ Zq M L) α false 1)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) (baseA _) α') :
    ((Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) = Fintype.card F ∧
        (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ α') = Fintype.card F) ∨
      (Fintype.card F ^ 2 ≤ (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) ∧
        Fintype.card F ^ 2 ≤ (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ α')) := by
  obtain ⟨μ, hμ, hrel₁, hrel₂⟩ := exists_conj_vertex h hc
  have hc' := ms22_iii _ h.hyp20 h.critDist_pos h.centHyp hc
  obtain ⟨α₁, hnat₁⟩ := natural_data_of_sp h hcard hF hα hnat hμ
  obtain ⟨α₂, hnat₂⟩ := natural_data_of_sp h hcard hF hα hnat hc'
  rcases shapes_at h hc hμ hrel₁ hrel₂ (sup_le h.L_le (pre_le h.le _)) hnat₁ le_sup_right
      (sup_le h.L_le (pre_le h.le _)) hnat₂ le_sup_right with
    ⟨-, -, h1, h2⟩ | ⟨h1, h2, -, -⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩

end Shapes

end CFSG.Quasithin.MS93.S33
