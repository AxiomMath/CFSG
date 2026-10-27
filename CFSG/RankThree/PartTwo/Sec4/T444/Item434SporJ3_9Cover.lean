module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporProof
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporJ3_9CoverLocal
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestJ3
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3OuterInvClosed

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint CFSG.LocalCores
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open Item434Alt (quotConj)
open CFSG.AGLEmbedding (kFactJ3OuterRank_closed kFactJ3OuterInvolution)

section Families


theorem item434Spor_J3_9Cover :
    Item434Spor_J3_9Cover := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h9 hZne
  obtain ⟨e₀⟩ := hL
  have : Finite (Spor .J3) := Finite.of_equiv _ e₀.toEquiv
  obtain ⟨b⟩ : Nonempty (NativeSporadic.Carrier .J3 ≃* Spor .J3) :=
    CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  have hJ : Nonempty (Spor .J3 ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) :=
    ⟨MulEquiv.refl _⟩
  have hOR := kFactJ3OuterRank_closed ⟨b⟩
  obtain ⟨hOut, -⟩ := hOR (Spor .J3) hJ
  have := CFSG.Sporadic.J3.isSimpleGroup_J3
  have : IsSimpleGroup (Spor .J3) := MulEquiv.isSimpleGroup (H := NativeSporadic.J3) b.symm
  have hcard : Nat.card (Spor .J3) = 50232960 := by
    rw [← Nat.card_congr b.toEquiv]
    exact CFSG.Sporadic.J3.card_J3
  have hcen : Subgroup.center (Spor .J3) = ⊥ :=
    Item434Spor.center_eq_bot_of_simple (by rw [hcard]; norm_num)
  have hout3 : ¬ 3 ∣ Nat.card (Outer (Spor .J3)) :=
    Item434Spor.not_three_dvd_card_outer_of_le_two hOut
  have hZ3 : Nat.card (Subgroup.center (layer G)) = 3 := by
    have hdvd : Nat.card (Subgroup.center (layer G)) ∣ 3 :=
      CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.card_center_dvd_three_of_J3
        hc.isQuasisimple hc.isPGroup_center_layer (e₀.trans b.symm)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (Subgroup.card_eq_one.mp h1) hZne
    · exact h3
  have hZA := Item434SporJ3.center_layer_le hc hZ3
  have hC3 : Nat.card (A ⊓ Subgroup.centralizer (layer G : Set G) : Subgroup G) = 3 := by
    have h1 := hc.card_inf_mul_card_layerStar
    have h9' : Nat.card hc.layerStar = 9 := h9
    rw [h9'] at h1
    omega
  have h9' : Nat.card (A.map (quotConj e₀)) = 9 := by
    rw [Item434Spor.card_map_quotConj hc e₀]
    exact h9
  set P := (A.map (quotConj e₀)).comap (MulAut.conj : Spor .J3 →* MulAut (Spor .J3)) with hP
  have hPmap : P.map MulAut.conj = A.map (quotConj e₀) :=
    Item434Kit.map_comap_conj_eq hc e₀ hout3
  have hinj := Item434Kit.conj_injective_of_center_eq_bot hcen
  have hP9 : Nat.card P = 9 := by
    rw [← Subgroup.card_map_of_injective hinj, hPmap, h9']
  have hPe : CFSG.Assembly.IsElemAbelian 3 P :=
    Item434Kit.isElemAbelian_of_map_injective hinj
      (hPmap ▸ Item434Kit.isElemAbelian_map_quotConj hc e₀)
  have hOuter : ∀ α : MulAut (Spor .J3), α ^ 2 = 1 →
      α ∉ (MulAut.conj : Spor .J3 →* MulAut (Spor .J3)).range →
      ∀ B : Subgroup (Spor .J3), IsMulCommutative B → (∀ x ∈ B, x ^ 3 = 1) → Nat.card B = 9 →
        ∃ x ∈ B, α x ≠ x := fun α hα2 hαout B hB hB3 hB9 =>
    kFactJ3OuterInvolution (Spor .J3) hJ α hα2 hαout B ⟨hB, hB3⟩ hB9
  rcases Item434SporJ3.j3_e9_split hOR (Spor .J3) hJ hPe.1 hPe.2 hP9 with hE | hgen
  · refine (Item434Kit.false_of_normalizer hc e₀ fun Y hY3 hAY => ?_).elim
    refine Item434SporJ3.eq_bot_of_normalized_nine hcen hE hOut hOuter hPe.1 hPe.2 hP9 hY3 ?_
    rw [hPmap]
    exact hAY
  · exact (hc.not_le (Item434SporJ3.layer_le_of_centralizer_gen hc e₀ hcen hZA hC3
      hPmap.symm hgen)).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
