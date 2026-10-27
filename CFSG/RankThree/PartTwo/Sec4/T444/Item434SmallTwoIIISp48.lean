module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIIKit
public import CFSG.RankThree.PartTwo.KFacts.K71InnerSp4
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.LocalAnalysis.SectionRank.EvenCover.Symplectic
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIIDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.RankThreeEven (projSp)
open KFacts

namespace Item434SmallTwoIII

section Fixed

variable {F : Type} [Field F] [Finite F] [CharP F 2]

@[expose] noncomputable def sp4E9 (F : Type) [Field F] : Subgroup (StatedSp 2 F) :=
  Subgroup.zpowers (sp4T F) ⊔ Subgroup.zpowers (sp4T' F)

omit [CharP F 2] in
theorem isElemAbelian_sp4E9 :
    CFSG.Assembly.IsElemAbelian 3 (sp4E9 F) ∧ Nat.card (sp4E9 F) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers (sp4T F)) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, sp4T_pow_three, one_zpow]
  have hcomm : ∀ b ∈ Subgroup.zpowers (sp4T F), b * sp4T' F = sp4T' F * b := by
    intro b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_left (sp4T_commute F) k).eq
  obtain ⟨hab, hcard⟩ := Sec5.isElemAbelian_sup_zpowers hT (sp4T'_not_mem_zpowers F)
    (sp4T'_pow_three F) hcomm
  refine ⟨hab, ?_⟩
  rw [sp4E9, hcard, Nat.card_zpowers, orderOf_eq_prime (sp4T_pow_three F) (sp4T_ne_one F)]

omit [Finite F] [CharP F 2] in
theorem sp4E9_le_range_spIncl (σ : F ≃+* F) : sp4E9 F ≤ (spIncl σ).range := by
  refine sup_le (Subgroup.zpowers_le.mpr ⟨_, spIncl_planeSp_ordThreeSL σ 0⟩)
    (Subgroup.zpowers_le.mpr ⟨_, spIncl_planeSp_ordThreeSL σ 1⟩)

theorem exists_fixed_E9_sp4 (α : MulAut (StatedProj (StatedSp 2 F))) (hα : α ^ 3 = 1)
    (hout : α ∉ (MulAut.conj : StatedProj (StatedSp 2 F) →*
      MulAut (StatedProj (StatedSp 2 F))).range) :
    ∃ E : Subgroup (StatedProj (StatedSp 2 F)), CFSG.Assembly.IsElemAbelian 3 E ∧
      Nat.card E = 9 ∧ ∀ x ∈ E, α x = x := by
  have hD : α ∉ (conjAut 2 F).range := by
    rintro ⟨A, rfl⟩
    exact hout (conjAut_mem_inner_of_charTwo A)
  obtain ⟨σ, -, H, rfl⟩ := sp4_even_order_three_field_descent α hα hD
  set c : StatedProj (StatedSp 2 F) →* StatedProj (StatedSp 2 F) :=
    ((conjAut 2 F H : StatedProj (StatedSp 2 F) ≃* StatedProj (StatedSp 2 F)) :
      StatedProj (StatedSp 2 F) →* StatedProj (StatedSp 2 F)) with hc
  have hinj : Function.Injective (c.comp (proj 2 F)) :=
    (conjAut 2 F H).injective.comp proj_injective_of_charTwo
  obtain ⟨hab, hcard⟩ := isElemAbelian_sp4E9 (F := F)
  refine ⟨(sp4E9 F).map (c.comp (proj 2 F)),
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ hab,
    by rw [Subgroup.card_map_of_injective hinj, hcard], ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hfix : fieldAut 2 F σ (proj 2 F y) = proj 2 F y :=
    (fieldAut_proj_eq_proj_iff σ y).mpr ((mem_range_spIncl_iff σ y).mp
      (sp4E9_le_range_spIncl σ hy))
  change (conjAut 2 F H * fieldAut 2 F σ * (conjAut 2 F H)⁻¹) (conjAut 2 F H (proj 2 F y)) =
    conjAut 2 F H (proj 2 F y)
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, hfix]

end Fixed

theorem exists_fixed_E9_projSp (φ : MulAut (projSp 2 (GaloisField 2 3))) (hφ : φ ^ 3 = 1)
    (hout : φ ∉ (MulAut.conj : projSp 2 (GaloisField 2 3) →*
      MulAut (projSp 2 (GaloisField 2 3))).range) :
    ∃ E : Subgroup (projSp 2 (GaloisField 2 3)), CFSG.Assembly.IsElemAbelian 3 E ∧
      Nat.card E = 9 ∧ ∀ x ∈ E, φ x = x := by
  set κ := projSpEquivStatedProj 2 (GaloisField 2 3)
  set α : MulAut (StatedProj (StatedSp 2 (GaloisField 2 3))) := MulAut.congr κ φ with hαdef
  have hα_apply : ∀ z, α z = κ (φ (κ.symm z)) := fun z => rfl
  have hα3 : α ^ 3 = 1 := by rw [hαdef, ← map_pow, hφ, map_one]
  have hαout : α ∉ (MulAut.conj : StatedProj (StatedSp 2 (GaloisField 2 3)) →*
      MulAut (StatedProj (StatedSp 2 (GaloisField 2 3)))).range := by
    rintro ⟨y, hy⟩
    apply hout
    refine ⟨κ.symm y, MulEquiv.ext fun x => ?_⟩
    have h1 : α (κ x) = κ (φ x) := by rw [hα_apply, MulEquiv.symm_apply_apply]
    have h2 : α (κ x) = y * κ x * y⁻¹ := by rw [← hy]; rfl
    rw [MulAut.conj_apply]
    apply κ.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← h1, h2]
  obtain ⟨E, hE, hE9, hfix⟩ := exists_fixed_E9_sp4 α hα3 hαout
  refine ⟨E.map κ.symm.toMonoidHom,
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ hE,
    by rw [Subgroup.card_map_of_injective κ.symm.injective, hE9], ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have h2 : κ (φ (κ.symm y)) = y := (hα_apply y).symm.trans (hfix y hy)
  change φ (κ.symm y) = κ.symm y
  apply κ.injective
  rw [h2, MulEquiv.apply_symm_apply]

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem center_layer_eq_bot_of_sp48 (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSp 2 (GaloisField 2 3)) :
    Subgroup.center (layer G) = ⊥ := by
  have : Group.IsPerfect (layer G) := h.isQuasisimple.1
  have hodd : Odd (Nat.card (Subgroup.center (layer G))) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_center_layer
    rw [hk]
    exact Odd.pow (by decide)
  exact CFSG.SectionRank.EvenCover.center_eq_bot_of_even_symplectic hodd
    (e₀.trans (projSpEquivStatedProj 2 (GaloisField 2 3)))

theorem forall_not_inducesOuter_sp48 (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSp 2 (GaloisField 2 3))
    (h9 : Nat.card (A.map (layerConj G)) = 9) : ∀ a ∈ A, ¬ InducesOuter a (layer G) :=
  forall_not_inducesOuter_of_fixed h (center_layer_eq_bot_of_sp48 h e₀) h9 e₀
    exists_fixed_E9_projSp

end Item434SmallTwoIII

section Families


theorem item434SmallTwoIII_Sp48_9_of (hI : Item434SmallTwoIII_Sp48_9Inner) :
    Item434SmallTwoIII_Sp48_9 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h9
  obtain ⟨e₀⟩ := hL
  exact hI G₀ hG₀ H G f hf hker A M Q hc ⟨e₀⟩ h9
    (Item434SmallTwoIII.forall_not_inducesOuter_sp48 hc e₀ h9)

end Families

end CFSG.RankThree.PartTwo.Sec4
