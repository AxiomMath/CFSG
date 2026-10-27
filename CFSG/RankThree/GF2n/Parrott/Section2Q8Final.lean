module

public import CFSG.RankThree.GF2n.Parrott.OThreeHConj
public import CFSG.RankThree.GF2n.Parrott.Section2Q8Transfer

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem exists_mem_O3H_notMem_zpowers (h : Tim79a.ParrottHyp z) :
    ∃ x : ↥(O3H D), x ∉ Subgroup.zpowers (⟨sigma1Nine (z := z) D,
      sigma1Nine_mem_O3H (z := z) D⟩ : ↥(O3H D)) := by
  by_contra hcon
  have hcon' : ∀ x : ↥(O3H D), x ∈ Subgroup.zpowers (⟨sigma1Nine (z := z) D,
      sigma1Nine_mem_O3H (z := z) D⟩ : ↥(O3H D)) := by
    intro x
    by_contra hx
    exact hcon ⟨x, hx⟩
  have hle : O3H D ≤ Subgroup.zpowers (sigma1Nine (z := z) D) := by
    intro x hx
    have hmem := hcon' ⟨x, hx⟩
    rw [Subgroup.mem_zpowers_iff] at hmem ⊢
    obtain ⟨k, hk⟩ := hmem
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have h1 : Nat.card ↥(O3H D) ≤ Nat.card ↥(Subgroup.zpowers (sigma1Nine (z := z) D)) := by
    refine Nat.card_le_card_of_injective
      (fun x : ↥(O3H D) => (⟨x.1, hle x.2⟩ : ↥(Subgroup.zpowers (sigma1Nine (z := z) D)))) ?_
    intro a b hab
    ext
    simpa using congrArg Subtype.val hab
  rw [card_O3H h D, Nat.card_zpowers, sigma1Nine_order (z := z) D] at h1
  norm_num at h1

theorem card_CJcomm_sigma1sigma2inv_eq_eight_of_lift (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    (hnorm : ∀ (g : ↥(H z)) (p : G),
      p ∈ ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ →
      (g : G) * p * (g : G)⁻¹ ∈
        ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆) :
    Nat.card ↥(CJcomm (z := z) (D := D) (sigma1Nine (z := z) D * σ₂⁻¹)) = 8 := by
  obtain ⟨x, hx⟩ := exists_mem_O3H_notMem_zpowers (z := z) (D := D) h
  have hxH : (x : ↥(H z)) ∉ Subgroup.zpowers (sigma1Nine (z := z) D) := by
    intro hmem
    rw [Subgroup.mem_zpowers_iff] at hmem
    obtain ⟨k, hk⟩ := hmem
    apply hx
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨k, by apply Subtype.ext; simpa using hk⟩
  obtain ⟨g, hg⟩ := exists_conj_eq_sigma1Nine_mul_inv_of_mem_O3H (z := z) (D := D) h
    (σ₂ := σ₂) hσ₂ hq₂ hc₂ x.2 hxH
  have hnormg : ∀ p : G,
      p ∈ ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ ↔
        (g : G) * p * (g : G)⁻¹ ∈
          ⁅(Subgroup.zpowers (sigma1Nine (z := z) D)).map (H z).subtype, J z⁆ := by
    intro p
    constructor
    · exact hnorm g p
    · intro hp
      have hq := hnorm g⁻¹ ((g : G) * p * (g : G)⁻¹) hp
      have hcoe : ((g⁻¹ : ↥(H z)) : G) = ((g : ↥(H z)) : G)⁻¹ := rfl
      have hgp : ((g⁻¹ : ↥(H z)) : G) * ((g : G) * p * (g : G)⁻¹) *
          (((g⁻¹ : ↥(H z)) : G))⁻¹ = p := by
        rw [hcoe]
        group
      rwa [hgp] at hq
  have hx1 : x ∉ Subgroup.zpowers (⟨sigma1Nine (z := z) D,
      sigma1Nine_mem_O3H (z := z) D⟩ : ↥(O3H D)) := hx
  exact card_CJcomm_sigma1sigma2inv_eq_eight_of_conj (z := z) (D := D) h σ₂ g x hx1
    (by simpa using hg) hnormg

end CFSG.RankThree.GF2n.Parrott
