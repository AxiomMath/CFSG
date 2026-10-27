module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4KS3
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Irr
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4Facts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S15223P4

namespace K

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

theorem mem_of_mk_mem_image {C : Subgroup G} (hOC : pCoreOf 2 (oTwoUpper H) ≤ C)
    (hCK : C ≤ oTwoUpper H) {x : G} (hxK : x ∈ oTwoUpper H)
    (hx : (QuotientGroup.mk ⟨x, oTwoUpper_le H hxK⟩ : OTwoQuot H) ∈ imageOTwoQuot H C) :
    x ∈ C := by
  obtain ⟨c, hcH, hcC, hcx⟩ := mem_imageOTwoQuot_iff.mp hx
  have h1 : (QuotientGroup.mk ⟨c⁻¹ * x, H.mul_mem (H.inv_mem hcH) (oTwoUpper_le H hxK)⟩ :
      OTwoQuot H) = 1 := by
    have : (⟨c⁻¹ * x, H.mul_mem (H.inv_mem hcH) (oTwoUpper_le H hxK)⟩ : ↥H) =
        (⟨c, hcH⟩ : ↥H)⁻¹ * ⟨x, oTwoUpper_le H hxK⟩ := rfl
    rw [this, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hcx, inv_mul_cancel]
  have h2 : c⁻¹ * x ∈ pCoreOf 2 H := (mk_eq_one_iff_mem_pCoreOf _).1 h1
  have h3 : c⁻¹ * x ∈ pCoreOf 2 (oTwoUpper H) := by
    rw [S15223.pCoreOf_oTwoUpper_eq H]
    exact ⟨(oTwoUpper H).mul_mem ((oTwoUpper H).inv_mem (hCK hcC)) hxK, h2⟩
  have := C.mul_mem hcC (hOC h3)
  rwa [mul_inv_cancel_left] at this

theorem exists_oTwoUpper_le (c : P4Ctx T Mc M H B₀ I X) {H₁ H₂ : Subgroup G}
    (hP : IsHPair H (V154 T Mc M) H₁ H₂) (hKS : oTwoUpper H ⊔ sOf152 T Mc M B₀ = H₁ ⊔ H₂)
    {C : Subgroup G} (hOC : pCoreOf 2 (oTwoUpper H) ≤ C) (hCK : C ≤ oTwoUpper H)
    (hC3 : (pCoreOf 2 (oTwoUpper H)).relIndex C = 3)
    (hSC : sOf152 T Mc M B₀ ≤ Subgroup.normalizer (C : Set G)) :
    oTwoUpper H₁ ≤ C ∨ oTwoUpper H₂ ≤ C := by
  obtain ⟨φ⟩ := c.quotH
  obtain ⟨e₁⟩ := hP.iso₁
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hSH : sOf152 T Mc M B₀ ≤ H := S_le_T152.trans c.sylowH.1
  have hCH : C ≤ H := hCK.trans hKH
  have hN3 : ∀ x ∈ imageOTwoQuot H (oTwoUpper H), x ^ 3 = 1 := by
    intro x hx
    have hx' : φ x ∈ S152N.W3.N0 := by
      rw [← S15223.map_imageOTwoQuot_oTwoUpper H φ]
      exact Subgroup.mem_map_of_mem _ hx
    apply φ.injective
    rw [map_pow, S15223.pow_three_of_mem_N0 _ hx', map_one]
  have hNcomm : ∀ a ∈ imageOTwoQuot H (oTwoUpper H), ∀ b ∈ imageOTwoQuot H (oTwoUpper H),
      a * b = b * a := by
    intro a ha b hb
    have ha' : φ a ∈ S152N.W3.N0 := by
      rw [← S15223.map_imageOTwoQuot_oTwoUpper H φ]
      exact Subgroup.mem_map_of_mem _ ha
    have hb' : φ b ∈ S152N.W3.N0 := by
      rw [← S15223.map_imageOTwoQuot_oTwoUpper H φ]
      exact Subgroup.mem_map_of_mem _ hb
    apply φ.injective
    rw [map_mul, map_mul]
    exact S15223.N0_comm _ _ ha' hb'
  have hNle : imageOTwoQuot H (oTwoUpper H) ≤ imageOTwoQuot H H₁ ⊔ imageOTwoQuot H H₂ := by
    rw [← imageOTwoQuot_sup hP.le₁.2 hP.le₂.2]
    exact imageOTwoQuot_mono (hp152_oTwoUpper_le hP)
  have hCN : imageOTwoQuot H C ≤ imageOTwoQuot H (oTwoUpper H) := imageOTwoQuot_mono hCK
  have hC' : Nat.card (imageOTwoQuot H C) = 3 := by
    have h1 := S143.card_imageOTwoQuot_mul hCH
    have hinf : C ⊓ pCoreOf 2 H = pCoreOf 2 (oTwoUpper H) := by
      apply le_antisymm
      · rw [S15223.pCoreOf_oTwoUpper_eq H]
        exact fun x hx => ⟨hCK hx.1, hx.2⟩
      · rw [S15223.pCoreOf_oTwoUpper_eq H]
        exact le_inf (by rw [← S15223.pCoreOf_oTwoUpper_eq H]; exact hOC) inf_le_right
    have h2 := Subgroup.relIndex_mul_card (pCoreOf 2 (oTwoUpper H)) C
    rw [inf_eq_left.2 hOC, hC3] at h2
    rw [hinf] at h1
    have hpos : 0 < Nat.card (pCoreOf 2 (oTwoUpper H)) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
  have hPP : imageOTwoQuot H H₁ ⊔ imageOTwoQuot H H₂ =
      imageOTwoQuot H (oTwoUpper H) ⊔ imageOTwoQuot H (sOf152 T Mc M B₀) := by
    rw [← imageOTwoQuot_sup hP.le₁.2 hP.le₂.2, ← hKS, imageOTwoQuot_sup hKH hSH]
  have hnorm : imageOTwoQuot H H₁ ≤ Subgroup.normalizer (imageOTwoQuot H C : Set (OTwoQuot H)) := by
    have hle : imageOTwoQuot H (oTwoUpper H) ⊔ imageOTwoQuot H (sOf152 T Mc M B₀) ≤
        Subgroup.normalizer (imageOTwoQuot H C : Set (OTwoQuot H)) :=
      sup_le (le_normalizer_of_commute fun a ha b hb => hNcomm a ha b (hCN hb))
        (S152Y.imageOTwoQuot_le_normalizer hSC)
    exact (le_sup_left.trans hPP.le).trans hle
  have key := eq_oTwoUpper_of_card_three e₁ (S15223.card_image_pair hP).2
    (S15223.imageOTwoQuot_commute hP.comm) (S15223.image_pair_inf hP) hN3 hNle hCN hC' hnorm
  have back : ∀ {H' : Subgroup G}, H' ≤ H → imageOTwoQuot H C = oTwoUpper (imageOTwoQuot H H') →
      oTwoUpper H' ≤ C := by
    intro H' hH' h x hx
    have hxK : x ∈ oTwoUpper H := oTwoUpper_mono hH' hx
    refine mem_of_mk_mem_image hOC hCK hxK ?_
    rw [h, ← S152Y.imageOTwoQuot_oTwoUpper hH']
    exact mem_imageOTwoQuot_iff.2 ⟨x, oTwoUpper_le H hxK, hx, rfl⟩
  rcases key with h | h
  · exact Or.inl (back hP.le₁.2 h)
  · exact Or.inr (back hP.le₂.2 h)

end K

end S15223P4

end CFSG.Quasithin
