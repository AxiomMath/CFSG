module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RowsProofL3Pi
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Kit

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434U38

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSU)

section Glue


@[expose] def U38K0 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* projSU 3 2 3) →
    ∀ E : Subgroup (MulAut X), CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
      ∀ Y : Subgroup (MulAut X), ¬ 3 ∣ Nat.card Y →
        E ≤ Subgroup.normalizer (Y : Set (MulAut X)) → Y = ⊥

theorem item434OtherU38TwentySeven_of_noE27 (hK0 : U38K0) : Item434OtherU38TwentySeven := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  exfalso
  have hZ : Subgroup.center (layer G) = ⊥ := by
    rcases hc.card_layerStar with h9 | ⟨_, hZ⟩
    · have : Nat.card hc.layerStar = 27 := h27
      omega
    · exact hZ
  have hCA : A ⊓ Subgroup.centralizer (layer G : Set G) = ⊥ := by
    have h1 := hc.card_inf_mul_card_layerStar
    have h2 : Nat.card hc.layerStar = 27 := h27
    rw [h2] at h1
    rw [← Subgroup.card_eq_one]
    omega
  have hA27 := Item434Kit.card_map_quotConj hc hCA (MulEquiv.refl (layer G ⧸ Subgroup.center (layer G)))
  have hAe := Item434Kit.isElemAbelian_map_quotConj hc (MulEquiv.refl (layer G ⧸ Subgroup.center (layer G)))
  refine Item434Kit.false_of_normalizer hc (MulEquiv.refl (layer G ⧸ Subgroup.center (layer G)))
    fun Y hY3 hYN => ?_
  exact hK0 (layer G ⧸ Subgroup.center (layer G)) hL _ hAe hA27 Y hY3 hYN

end Glue

end CFSG.RankThree.PartTwo.Sec4.Item434U38
