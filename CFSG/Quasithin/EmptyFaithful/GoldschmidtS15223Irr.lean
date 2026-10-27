module

public import CFSG.Quasithin.EmptyFaithful.S152U21
public import CFSG.Quasithin.EmptyFaithful.S152NBasic
public import CFSG.Quasithin.EmptyFaithful.S152Y06
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223W3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Quot
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SubnormalCore

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S15223

variable {G : Type} [Group G]

theorem oTwoUpper_normal_subgroupOf (H : Subgroup G) : ((oTwoUpper H).subgroupOf H).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le H)).mpr (le_normalizer_oTwoUpper H)

theorem le_normalizer_pCoreOf_oTwoUpper (H : Subgroup G) :
    H ≤ Subgroup.normalizer (pCoreOf 2 (oTwoUpper H) : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    ((CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 _).trans (oTwoUpper_le H))).mp
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_subgroupOf 2 _ H (oTwoUpper_le H)
      (oTwoUpper_normal_subgroupOf H))

theorem pCoreOf_oTwoUpper_eq [Finite G] (H : Subgroup G) :
    pCoreOf 2 (oTwoUpper H) = oTwoUpper H ⊓ pCoreOf 2 H := by
  apply le_antisymm
  · exact le_inf (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 _)
      (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 _ H
        (oTwoUpper_le H) (oTwoUpper_normal_subgroupOf H))
  · refine CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _ inf_le_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
        (le_normalizer_inf_of_both Subgroup.le_normalizer
          ((oTwoUpper_le H).trans (le_normalizer_pCoreOf 2 H))))
      ((CFSG.RankThreeEvenClassification.Helpers.pCoreOf_isPGroup 2 H).to_inf_right)

section Image

variable [Finite G]

theorem map_imageOTwoQuot_oTwoUpper (H : Subgroup G) (φ : OTwoQuot H ≃* S152N.W3) :
    (imageOTwoQuot H (oTwoUpper H)).map (φ : OTwoQuot H →* S152N.W3) = S152N.W3.N0 := by
  rw [S152Y.imageOTwoQuot_oTwoUpper le_rfl, imageOTwoQuot_self_top, ← oTwoUpper_map,
    Subgroup.map_top_of_surjective _ φ.surjective]
  exact oTwoUpper_top_eq_N0

end Image

theorem input15209Irr_of (h15208 : StageLemma15208) : Input15209Irr := by
  intro G _ _ T Mc M hs H hH
  obtain ⟨φ⟩ := h15208 G T Mc M hs H hH
  have hT : IsSylowTwoOf T H := S152N.isSylowTwoOf_hStar hs hH
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hHK : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  have hOK := pCoreOf_oTwoUpper_eq H
  have hKimg := map_imageOTwoQuot_oTwoUpper H φ
  have hP := S152N.isSylowTwoOf_image hT φ
  have hN0 : S152N.W3.N0 ≠ ⊥ := by
    intro h
    have := S152N.W3.card_N0
    rw [h, Subgroup.card_bot] at this
    omega
  unfold IsIrredOnSection
  refine ⟨?_, hT.1.trans hHK, hT.1.trans (le_normalizer_pCoreOf_oTwoUpper H), ?_⟩
  · refine lt_of_le_of_ne (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 _) fun h => hN0 ?_
    have hle : oTwoUpper H ≤ pCoreOf 2 H := by
      have h1 : oTwoUpper H = oTwoUpper H ⊓ pCoreOf 2 H := by rw [← hOK]; exact h.symm
      exact h1.trans_le inf_le_right
    rw [← hKimg, eq_bot_iff]
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨x, hxH, hxK, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    have : (QuotientGroup.mk ⟨x, hxH⟩ : OTwoQuot H) = 1 :=
      (mk_eq_one_iff_mem_pCoreOf ⟨x, hxH⟩).mpr (hle hxK)
    simp [this]
  · intro W hOW hWK hTW
    set C : Subgroup S152N.W3 := (imageOTwoQuot H W).map (φ : OTwoQuot H →* S152N.W3) with hC
    have hCN : C ≤ S152N.W3.N0 := by
      rw [← hKimg]
      exact Subgroup.map_mono (imageOTwoQuot_mono hWK)
    have hinv : ∀ p ∈ (imageOTwoQuot H T).map (φ : OTwoQuot H →* S152N.W3), ∀ c ∈ C,
        p * c * p⁻¹ ∈ C := by
      rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      refine ⟨u * v * u⁻¹, ?_, by simp⟩
      exact (Subgroup.mem_normalizer_iff.mp (S152Y.imageOTwoQuot_le_normalizer hTW hu) v).mp hv
    rcases eq_bot_or_eq_N0_of_sylow hP hCN hinv with h | h
    · left
      refine le_antisymm (fun w hw => ?_) hOW
      have hwH : w ∈ H := hKH (hWK hw)
      have h1 : (QuotientGroup.mk ⟨w, hwH⟩ : OTwoQuot H) ∈ imageOTwoQuot H W :=
        mem_imageOTwoQuot_iff.mpr ⟨w, hwH, hw, rfl⟩
      have h2 : (φ : OTwoQuot H →* S152N.W3) (QuotientGroup.mk ⟨w, hwH⟩) ∈ C :=
        Subgroup.mem_map_of_mem _ h1
      rw [h, Subgroup.mem_bot] at h2
      have h3 : (QuotientGroup.mk ⟨w, hwH⟩ : OTwoQuot H) = 1 := by
        apply φ.injective
        simpa using h2
      rw [hOK]
      exact ⟨hWK hw, (mk_eq_one_iff_mem_pCoreOf ⟨w, hwH⟩).mp h3⟩
    · right
      have hW : imageOTwoQuot H W = imageOTwoQuot H (oTwoUpper H) :=
        Subgroup.map_injective (f := (φ : OTwoQuot H →* S152N.W3)) φ.injective
          (h.trans hKimg.symm)
      refine le_antisymm hWK (fun x hx => ?_)
      have hxH : x ∈ H := hKH hx
      have h1 : (QuotientGroup.mk ⟨x, hxH⟩ : OTwoQuot H) ∈ imageOTwoQuot H W := by
        rw [hW]
        exact mem_imageOTwoQuot_iff.mpr ⟨x, hxH, hx, rfl⟩
      obtain ⟨w, hwH, hwW, hwx⟩ := mem_imageOTwoQuot_iff.mp h1
      have h2 : (⟨w, hwH⟩ : ↥H)⁻¹ * ⟨x, hxH⟩ ∈ CFSG.Open.pCore 2 ↥H := QuotientGroup.eq.mp hwx
      have h3 : w⁻¹ * x ∈ pCoreOf 2 H := by
        unfold pCoreOf
        exact Subgroup.mem_map.mpr ⟨_, h2, rfl⟩
      have h4 : w⁻¹ * x ∈ pCoreOf 2 (oTwoUpper H) := by
        rw [hOK]
        exact ⟨(oTwoUpper H).mul_mem ((oTwoUpper H).inv_mem (hWK hwW)) hx, h3⟩
      have h5 := W.mul_mem hwW (hOW h4)
      rwa [mul_inv_cancel_left] at h5

end S15223

end CFSG.Quasithin
