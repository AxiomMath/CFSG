module

public import CFSG.RankThree.PartTwo.Sec4.Item419ThetaProofTools
public import CFSG.RankThree.PartTwo.Sec4.Item419Res2ProofAll
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCover

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU projSp)
open CFSG.Blueprint
open Sec21 Sec21.Item211Proof

section Theta

theorem item4_19ThetaJ3_of_NJ3 (h419 : Item4_19NJ3) (h45 : Item4_5)
    (h41 : Item4_1LargePrime) : Item4_19ThetaJ3 := by
  intro G _ _ hG L hL A c hA h81 hsec hc a ha hac K hK htype hF
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hA.prop
  have hAp : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hAe.2 x x.2)⟩
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    h45 G hG A hAp (Or.inr ⟨hAe, 4, by norm_num, h81⟩) L hL
  have hCA : A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c := by
    rw [Sec13.sectionCentralizer_eq_inf hAL] at hsec
    exact SetLike.coe_injective hsec
  have hcA : c ∈ A :=
    (show c ∈ A ⊓ thetaQuotCentralizer L from hCA ▸ Subgroup.mem_zpowers c).1
  have hq : IsQuasisimple (lBar L) := hL.2.2
  have hΛ : SectionFourHyp ↥(L ⊔ A) := Census.sectionFourHyp_subgroup hG (L ⊔ A)
  obtain ⟨Φ₀, hΦ₀⟩ := exists_lEquiv hAL
  have hX : SectionFourHyp (QuotX L A) := sectionFourHyp_quotX h41 hΛ hAp hAL Φ₀ hq
  have hL₁ : IsComponent (lOne L A) := isComponent_lOne hAL Φ₀ hq
  have hA₁ := maximal_aOne (L := L) hAe fun B hB hAB => le_antisymm (hA.2 hB hAB) hAB
  have h81₁ : Nat.card (aOne L A) = 3 ^ 4 := by
    rw [← Nat.card_congr (aEquiv (L := L) hAp).toEquiv, h81]
  have hA₁c := aOne_inf_centralizer hAp hAL hcA hCA
  have hc₁ : orderOf (piX L A ⟨c, Subgroup.mem_sup_right hcA⟩) = 3 := by
    have h1 : (piX L A ⟨c, Subgroup.mem_sup_right hcA⟩) =
        ((aEquiv (L := L) hAp ⟨c, hcA⟩ : aOne L A) : QuotX L A) := rfl
    rw [h1, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hc
  have ha₁ := piX_mem_aOne (L := L) ha
  have ha₁c : piX L A ⟨a, Subgroup.mem_sup_right ha⟩ ∉
      Subgroup.zpowers (piX L A ⟨c, Subgroup.mem_sup_right hcA⟩) := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    apply hac
    have h1 : aEquiv (L := L) hAp (⟨c, hcA⟩ ^ k) = aEquiv (L := L) hAp ⟨a, ha⟩ := by
      apply Subtype.ext
      rw [map_zpow, Subgroup.coe_zpow, aEquiv_apply, aEquiv_apply]
      exact hk
    have h2 := (aEquiv (L := L) hAp).injective h1
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val h2⟩
  obtain ⟨hK₁le, hK₁c, htype₁, ⟨eK⟩⟩ := Item419ThetaProof.isComponent_kOne hL hAp hAL ha hK htype
  have hF₁ := Item419ThetaProof.card_le_of_mem_partTwoF_quotX (L := L) (A := A) hF
  rcases h419 (QuotX L A) hX (lOne L A) hL₁ (aOne L A) _ hA₁ h81₁ hA₁c hc₁ _ ha₁ ha₁c _ hK₁le
      hK₁c htype₁ hF₁ with hk | ⟨hA6, hL96⟩ | ⟨hA6, hJ⟩
  · exact Or.inl (hk.imp (inducesStdKind_of_lOne hAL hΦ₀ ha) (inducesStdKind_of_lOne hAL hΦ₀ ha))
  · obtain ⟨eA⟩ := hA6
    rcases hL96 with h9 | h6
    · obtain ⟨e9⟩ := h9
      exact Or.inr (Or.inl ⟨⟨eK.symm.trans eA⟩, Or.inl ⟨Φ₀.trans e9⟩⟩)
    · obtain ⟨e6⟩ := h6
      exact Or.inr (Or.inl ⟨⟨eK.symm.trans eA⟩, Or.inr ⟨Φ₀.trans e6⟩⟩)
  · obtain ⟨eA⟩ := hA6
    exact Or.inr (Or.inr ⟨⟨eK.symm.trans eA⟩,
      Sec8.Item812Res5.nonempty_center_quot_of_mulEquiv Φ₀.symm hJ⟩)

theorem item4_19ThetaJ3_of_census
    (h417 : Item4_17) (h46 : Item4_6) (hAut : K419AutThree) (hOne : K419OneFieldCensus)
    (hU4 : K419U4Odd) (hC : K419UnitaryCensus) (h45 : Item4_5) (h41 : Item4_1LargePrime) :
    Item4_19ThetaJ3 :=
  item4_19ThetaJ3_of_NJ3 (item4_19NJ3_of_res2_census h417 h46 hAut hOne hU4 hC) h45 h41

end Theta

end CFSG.RankThree.PartTwo.Sec4

