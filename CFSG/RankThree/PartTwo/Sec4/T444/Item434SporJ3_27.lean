module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporProof
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporJ3_27Group
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporJ3_27Local
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3OuterInvClosed

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Blueprint CFSG.LocalCores
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open Item434Alt (quotConj)
open CFSG.AGLEmbedding (kFactJ3OuterRank_closed kFactJ3OuterInvolution)

section Families


theorem item434Spor_J3_27 :
    Item434Spor_J3_27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  obtain ⟨e₀⟩ := hL
  have : Finite (Spor .J3) := Finite.of_equiv _ e₀.toEquiv
  obtain ⟨b⟩ : Nonempty (NativeSporadic.Carrier .J3 ≃* Spor .J3) :=
    CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  have hJ : Nonempty (Spor .J3 ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) :=
    ⟨MulEquiv.refl _⟩
  have hOR := kFactJ3OuterRank_closed ⟨b⟩
  obtain ⟨hOut, -⟩ := hOR (Spor .J3) hJ
  obtain ⟨S, Z, φ, hsetup⟩ := Item434SporJ3.exists_outerSetup hOR (Spor .J3) hJ
  have := CFSG.Sporadic.J3.isSimpleGroup_J3
  have : IsSimpleGroup (Spor .J3) := MulEquiv.isSimpleGroup (H := NativeSporadic.J3) b.symm
  have hcard : Nat.card (Spor .J3) = 50232960 := by
    rw [← Nat.card_congr b.toEquiv]
    exact CFSG.Sporadic.J3.card_J3
  have hcen : Subgroup.center (Spor .J3) = ⊥ :=
    Item434Spor.center_eq_bot_of_simple (by rw [hcard]; norm_num)
  have hZ : Subgroup.center (layer G) = ⊥ := by
    rcases hc.card_layerStar with h9 | ⟨-, hZ⟩
    · have : Nat.card hc.layerStar = 27 := h27
      omega
    · exact hZ
  have hout3 : ¬ 3 ∣ Nat.card (Outer (Spor .J3)) :=
    Item434Spor.not_three_dvd_card_outer_of_le_two hOut
  refine (Item434Kit.false_of_normalizer hc e₀ fun Y hY3 hAY => ?_).elim
  have h27' : Nat.card (A.map (quotConj e₀)) = 27 := by
    rw [Item434Spor.card_map_quotConj hc e₀]
    exact h27
  set P := (A.map (quotConj e₀)).comap (MulAut.conj : Spor .J3 →* MulAut (Spor .J3)) with hP
  have hPmap : P.map MulAut.conj = A.map (quotConj e₀) :=
    Item434Kit.map_comap_conj_eq hc e₀ hout3
  have hinj := Item434Kit.conj_injective_of_center_eq_bot hcen
  have hP27 : Nat.card P = 27 := by
    rw [← Subgroup.card_map_of_injective hinj, hPmap, h27']
  have hPe : CFSG.Assembly.IsElemAbelian 3 P :=
    Item434Kit.isElemAbelian_of_map_injective hinj
      (hPmap ▸ Item434Kit.isElemAbelian_map_quotConj hc e₀)
  refine Item434SporJ3.eq_bot_of_normalized hcen
    (fun B hB hB3 hB9 => Item434SporJ3.isPGroup_centralizer hsetup hB hB3 hB9) hOut
    (fun α hα2 hαout B hB hB3 hB9 =>
      kFactJ3OuterInvolution (Spor .J3) hJ α hα2 hαout B ⟨hB, hB3⟩ hB9)
    hPe.1 hPe.2 hP27 hY3 ?_
  rw [hPmap]
  exact hAY

end Families

end CFSG.RankThree.PartTwo.Sec4
