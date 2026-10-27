module

public import CFSG.LocalAnalysis.StandardType.GGHalfCoords
public import CFSG.LocalAnalysis.StandardType.GGHalfBasic
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaEq
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveTwoGroup

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
  (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂)

include h

private theorem bs_eq_of_normalizes_two {S₂ : Subgroup G} (hS₂2 : IsPGroup 2 S₂) (hS₂ne : S₂ ≠ ⊥)
    (hBsS₂ : Bs ≤ Subgroup.normalizer (S₂ : Set G)) : Bs = B := by
  obtain ⟨hp, hBsE, -, -, -⟩ := GGConfig.tableB_facts h.cfg
  haveI := Fact.mk hp
  have hS : LargeEvenSStar p B x L := h.cfg.1.2.2.2.2.2.2.1
  have hBBs : B ≤ Bs := h.cfg.2.1.1
  have hBsP : IsPGroup p Bs := TableB.isPGroup_of_isElemAbelian hBsE
  obtain ⟨e, he⟩ := hBsP.exists_card_eq
  have h1 := CFSG.LargeEvenClassification.Helpers.elementary_pRank_card hp.one_lt Bs hBsE he
  have h2 := CFSG.LargeEvenClassification.Helpers.pRank_mono hp.one_lt hBsS₂
  have h3 := CFSG.LargeEvenClassification.Helpers.pRank_le_twoLocalPRank hp.one_lt _
    (⟨S₂, hS₂ne, hS₂2, rfl⟩ : CFSG.Open.IsTwoLocal (Subgroup.normalizer (S₂ : Set G)))
  rw [h1] at h2
  have hle : e ≤ LargeEvenTwoLocalRank p G := h2.trans h3
  have hcardB : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hS.1.2.1
  have hcard : Nat.card Bs ≤ Nat.card B := by
    rw [he, hcardB]
    exact Nat.pow_le_pow_right hp.pos hle
  exact (Subgroup.eq_of_le_of_card_ge hBBs hcard).symm

theorem bs_eq : Bs = B := by
  obtain ⟨U, hU1, hU2, hUt⟩ := exists_two_group_normalized_by_halfTorus
  have hinj : Function.Injective φ₁ := h.coords.inj₁
  have key : ∀ c ∈ Bs, ∀ u ∈ U, c * φ₁ u * c⁻¹ ∈ U.map φ₁ := by
    intro c hc u hu
    obtain ⟨t, ht, hct⟩ := h.coords.actL c hc
    have hl : φ₁ u ∈ L := by rw [← h.coords.range₁]; exact ⟨u, rfl⟩
    rw [hct (φ₁ u) hl]
    exact ⟨t * u * t⁻¹, hUt t ht u hu, by simp only [map_mul, map_inv]⟩
  refine bs_eq_of_normalizes_two h (S₂ := U.map φ₁) (hU2.map φ₁) ?_ ?_
  · intro hbot
    exact hU1 ((Subgroup.map_eq_bot_iff_of_injective U hinj).mp hbot)
  · intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro g
    change g ∈ U.map φ₁ ↔ c * g * c⁻¹ ∈ U.map φ₁
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact key c hc u hu
    · intro hg
      obtain ⟨u, hu, hug⟩ := hg
      have hk := key c⁻¹ (Bs.inv_mem hc) u hu
      have e : c⁻¹ * φ₁ u * c⁻¹⁻¹ = g := by rw [hug]; group
      rwa [e] at hk

end GGHalfCtx

end CFSG.StandardType

end
