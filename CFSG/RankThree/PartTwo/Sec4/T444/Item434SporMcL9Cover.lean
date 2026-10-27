module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporMcL9Local
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporNineKit
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporJ3_9CoverGroup
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestMcL

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint CFSG.LocalCores
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open Item434Alt (quotConj)
open Item434Kit (layerQuot layerQuot_surjective ker_layerQuot)
open CFSG.Sporadic.Schreier (mclP)

section Families


theorem item434Spor_McL_9Cover :
    Item434Spor_McL_9Cover := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h9 hZne
  obtain ⟨e₀⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  have b₀ : NativeSporadic.McL ≃* Spor .McL := b
  have eP : NativeSporadic.McL ≃* mclP := CFSG.Sporadic.Schreier.mclPermEquiv
  have e : layer G ⧸ Subgroup.center (layer G) ≃* mclP := e₀.trans (b₀.symm.trans eP)
  have : IsSimpleGroup (layer G ⧸ Subgroup.center (layer G)) := hc.isQuasisimple.2.1
  have : IsSimpleGroup mclP := e.symm.isSimpleGroup
  have hcen : Subgroup.center mclP = ⊥ :=
    Item434Spor.center_eq_bot_of_simple (by rw [CFSG.Sporadic.Schreier.card_mclP]; norm_num)
  have hout : ¬ 3 ∣ Nat.card (Outer mclP) :=
    Item434Spor.not_three_dvd_card_outer_of_le_two CFSG.Sporadic.SmallOddCore.mcl_outer_card_le
  have hZ3 : Nat.card (Subgroup.center (layer G)) = 3 := by
    have hdvd : Nat.card (Subgroup.center (layer G)) ∣ 3 :=
      CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.card_center_dvd_three_of_McL
        hc.isQuasisimple hc.isPGroup_center_layer (e₀.trans b₀.symm)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (Subgroup.card_eq_one.mp h1) hZne
    · exact h3
  have hZA := Item434SporJ3.center_layer_le hc hZ3
  have hC3 : Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) = 3 := by
    have h1 := hc.card_inf_mul_card_layerStar
    have h9' : Nat.card hc.layerStar = 9 := h9
    rw [h9'] at h1
    omega
  have h9' : Nat.card (A.map (quotConj e)) = 9 := by
    rw [Item434Spor.card_map_quotConj hc e]
    exact h9
  set P := (A.map (quotConj e)).comap (MulAut.conj : mclP →* MulAut mclP) with hP
  have hPmap : P.map MulAut.conj = A.map (quotConj e) :=
    Item434Kit.map_comap_conj_eq hc e hout
  have hinj := Item434Kit.conj_injective_of_center_eq_bot hcen
  have hP9 : Nat.card P = 9 := by
    rw [← Subgroup.card_map_of_injective hinj, hPmap, h9']
  have hPe : CFSG.Assembly.IsElemAbelian 3 P :=
    Item434Kit.isElemAbelian_of_map_injective hinj
      (hPmap ▸ Item434Kit.isElemAbelian_map_quotConj hc e)
  have hZexp : ∀ z ∈ (layerQuot e).ker, z ^ 3 = 1 := by
    intro z hz
    rw [ker_layerQuot] at hz
    have := pow_card_eq_one' (G := Subgroup.center (layer G)) (x := ⟨z, hz⟩)
    rw [hZ3] at this
    exact congrArg Subtype.val this
  refine (Item434SporNine.false_of_lift_e81 hc e hcen hZA hC3 hPmap.symm hP9 ?_).elim
  intro u hu _
  obtain ⟨E, hE, hE81, hEu⟩ := Item434SporMcL9.exists_lift_e81 (layerQuot e)
    (layerQuot_surjective e) (by rw [ker_layerQuot]) hZexp (hPe.2 u hu)
  exact ⟨E, hE, hE81, fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hEu x hx)⟩

end Families

end CFSG.RankThree.PartTwo.Sec4
