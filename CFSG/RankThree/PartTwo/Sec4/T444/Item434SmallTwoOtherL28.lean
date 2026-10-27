module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporKit
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISL28
import CFSG.RankThree.PartTwo.KFacts.K71L28Cent

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Assembly.RankThreeEven (projSL)
open Item434Kit Item434Alt
open scoped MatrixGroups

namespace Item434SmallTwoOther

theorem psl28_eq_bot_of_normalizes_conj {u : PSL(2, GaloisField 2 3)} (hu3 : u ^ 3 = 1)
    (hu1 : u ≠ 1) {Y : Subgroup (MulAut PSL(2, GaloisField 2 3))} (hY3 : ¬ 3 ∣ Nat.card Y)
    (hYu : ∀ ν ∈ Y, MulAut.conj u * ν * (MulAut.conj u)⁻¹ ∈ Y) : Y = ⊥ := by
  set ψ := KFacts.sl2EquivPSL28.symm
  have hinj : Function.Injective
      (MulAut.conj : PSL(2, GaloisField 2 3) →* MulAut PSL(2, GaloisField 2 3)) :=
    (injective_iff_map_eq_one _).mpr fun y hy => KFacts.eq_one_of_conj_eq_one_psl28 hy
  set Y₀ := Y.comap MulAut.conj
  have hY₀3 : ¬ 3 ∣ Nat.card Y₀ := by
    intro h3
    apply hY3
    rw [← Subgroup.card_map_of_injective hinj] at h3
    exact h3.trans (Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ _))
  set W := Y₀.map (ψ : PSL(2, GaloisField 2 3) →* SL(2, GaloisField 2 3)) with hW
  have hW3 : ¬ 3 ∣ Nat.card W := by
    rw [hW, Subgroup.card_map_of_injective ψ.injective]
    exact hY₀3
  have hxW : ∀ y ∈ W, ψ u * y * (ψ u)⁻¹ ∈ W := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨u * z * u⁻¹, ?_, ?_⟩
    · change MulAut.conj (u * z * u⁻¹) ∈ Y
      rw [map_mul, map_mul, map_inv]
      exact hYu _ hz
    · change ψ (u * z * u⁻¹) = ψ u * ψ z * (ψ u)⁻¹
      rw [map_mul, map_mul, map_inv]
  have hWbot := Item434SmallTwoIII.sl28_eq_bot_of_normalizes_coprime (x := ψ u)
    (by rw [← map_pow, hu3, map_one]) (ψ.map_ne_one_iff.mpr hu1) hW3 hxW
  have hY₀bot : Y₀ = ⊥ := by
    rw [hW, Subgroup.map_eq_bot_iff_of_injective _ ψ.injective] at hWbot
    exact hWbot
  rw [eq_bot_iff]
  intro ν hν
  rw [Subgroup.mem_bot]
  obtain ⟨y, rfl⟩ := KFacts.exists_conj_of_pow_eq_one_psl28 hY3 (KFacts.pow_card_eq_one_of_mem hν)
  have hy : y ∈ Y₀ := hν
  rw [hY₀bot, Subgroup.mem_bot] at hy
  rw [hy, map_one]

section Ctx

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem exists_conj_mem_map_quotConj_l28 (h : Ctx434Core G A M Q)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* PSL(2, GaloisField 2 3)) :
    ∃ u : PSL(2, GaloisField 2 3), u ^ 3 = 1 ∧ u ≠ 1 ∧ MulAut.conj u ∈ A.map (quotConj e₀) := by
  choose g σ hgσ using fun β : MulAut PSL(2, GaloisField 2 3) =>
    KFacts.exists_pglAction_mul_psl2FieldAut β
  have hcard : 9 ≤ Nat.card (A.map (quotConj e₀)) := by
    rw [Item434Spor.card_map_quotConj h e₀]
    rcases h.card_layerStar with h9 | ⟨h27, -⟩ <;> omega
  have : Finite (GaloisField 2 3 ≃+* GaloisField 2 3) :=
    Nat.finite_of_card_ne_zero (by rw [KFacts.card_ringAut_galoisField_two_three]; norm_num)
  have hni : ¬ Function.Injective fun β : A.map (quotConj e₀) => σ β := by
    intro hinj
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [KFacts.card_ringAut_galoisField_two_three] at h1
    omega
  obtain ⟨⟨β₁, hβ₁⟩, ⟨β₂, hβ₂⟩, hσ, hne⟩ := Function.not_injective_iff.mp hni
  have hσ' : σ β₁ = σ β₂ := hσ
  have hβ : β₁ * β₂⁻¹ = pglAction (GaloisField 2 3) (g β₁ * (g β₂)⁻¹) := by
    have e1 := hgσ β₁
    have e2 := hgσ β₂
    rw [hσ'] at e1
    calc β₁ * β₂⁻¹ = pglAction (GaloisField 2 3) (g β₁) *
          psl2FieldAut (GaloisField 2 3) (σ β₂) * (pglAction (GaloisField 2 3) (g β₂) *
            psl2FieldAut (GaloisField 2 3) (σ β₂))⁻¹ := by
          rw [← e1, ← e2]
      _ = pglAction (GaloisField 2 3) (g β₁ * (g β₂)⁻¹) := by
          rw [map_mul, map_inv]
          group
  obtain ⟨u, hu⟩ := KFacts.toPGL_surjective_psl28 (g β₁ * (g β₂)⁻¹)
  rw [← hu, pglAction_toPGL] at hβ
  have hmem : β₁ * β₂⁻¹ ∈ A.map (quotConj e₀) := mul_mem hβ₁ (inv_mem hβ₂)
  refine ⟨u, KFacts.eq_one_of_conj_eq_one_psl28 ?_, fun hu1 => hne ?_, hβ ▸ hmem⟩
  · rw [map_pow, ← hβ]
    exact (isElemAbelian_map_quotConj h e₀).2 _ hmem
  · rw [hu1, map_one, mul_inv_eq_one] at hβ
    exact Subtype.ext hβ

theorem false_of_l28 (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* projSL 2 (GaloisField 2 3)) : False := by
  set e₀ := e.trans (projSLEquivPSL (GaloisField 2 3))
  obtain ⟨u, hu3, hu1, huA⟩ := exists_conj_mem_map_quotConj_l28 h e₀
  refine false_of_normalizer h e₀ fun Y hY3 hAY => ?_
  exact psl28_eq_bot_of_normalizes_conj hu3 hu1 hY3 fun ν hν =>
    (Subgroup.mem_normalizer_iff.mp (hAY huA) ν).mp hν

end Ctx

end Item434SmallTwoOther

section Families


theorem item434SmallTwoOtherAtL28 : Item434SmallTwoOtherAtL28 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨e⟩ := hL
  exact (Item434SmallTwoOther.false_of_l28 hc e).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
