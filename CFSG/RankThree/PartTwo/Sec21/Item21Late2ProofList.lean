module

public import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
public import CFSG.RankThree.PartTwo.Sec21.Item211Res3ProofLocal
import CFSG.RankThree.PartTwo.Sec21.Item231Of
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Sec6.Item612

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Item211Proof

section Certs


namespace Item21Late2Proof

variable {G : Type} [Group G] [Finite G]

theorem list211_of_mem_lZeroStarAt (h417 : Sec4.Item4_17) (h611 : Sec6.Item6_11_1)
    (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (h41 : Sec4.Item4_1LargePrime) {A : Subgroup G}
    (hstd : Sec21Std G A) {b : G} (hbA : b ∈ A) (hb1 : b ≠ 1) {Y : Subgroup G}
    (hY : Y ∈ lZeroStarAt A b) : (Nat.card A = 3 ^ 3 ∨ Nat.card A = 3 ^ 4) ∧ List211 A b Y := by
  refine ⟨card_eq_of_mem_partTwoS h611 hstd, ?_⟩
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hstd.mem_S.1.1
  have hA : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hAe.2 a a.2)⟩
  have hYb : Y ∈ thetaComponentsAt 3 b := (lZeroStarAt_subset A b) hY
  have hYC : Y ≤ Subgroup.centralizer ({b} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hYb
  have hAC : A ≤ Subgroup.centralizer ({b} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hbA⟩))
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hstd.standing.toTheoremFourHyp hAe hbA hb1
      Y hYb
  have hq : IsQuasisimple (lBar Y) := by
    obtain ⟨Y', hY', hYY'⟩ := hYb
    rw [← hYY']
    exact LocalCores.isQuasisimple_of_mulEquiv (Sec13.thetaQuotEquivSub _ Y') hY'.2.2
  have hYs : Y ∈ lStar A := lZeroStar_subset_lStar A (lZeroStarAt_subset_lZeroStar A b hY)
  have hb3 : orderOf b = 3 := orderOf_eq_prime (hAe.2 b hbA) hb1
  have hCA : A ⊓ Sec4.thetaQuotCentralizer Y = Subgroup.zpowers b := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr
      ⟨hbA, Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hYb⟩) ?_
    rw [Nat.card_zpowers, hb3]
    exact Sec6.card_le_three_of_isCyclic (h66 G hstd.standing A hstd.mem_S Y hYs)
      fun x hx => hAe.2 x hx.1
  have hΛ : SectionFourHyp ↥(Y ⊔ A) := hstd.standing.toTheoremFourHyp.sectionFourHyp
    (fun htop => centralizer_ne_top hstd.standing.toTheoremFourHyp hb1
      (eq_top_iff.mpr (htop ▸ sup_le hYC hAC)))
  obtain ⟨Φ₀, hΦ₀⟩ := exists_lEquiv hAY
  have hX : SectionFourHyp (QuotX Y A) := sectionFourHyp_quotX h41 hΛ hA hAY Φ₀ hq
  obtain ⟨eAut⟩ := nonempty_autIn_lOne_equiv hA hAY
  obtain ⟨eX⟩ := nonempty_quotX_equiv_lBarA hYb hAC hA hAY
  obtain ⟨m, hm⟩ := hA.exists_card_eq
  obtain ⟨E₀, hE₀, hE₀A, -, U₀, hU₀, hU₀E⟩ :=
    mem_lZeroUnion_iff.mp (lZeroStar_subset_lZeroUnion A (lZeroStarAt_subset_lZeroStar A b hY))
  obtain ⟨hE₁, hE₁A, T, hT, hTc⟩ :=
    exists_eOne hA hAY (Late.isE27_of_mem_partTwoE hE₀) hE₀A hU₀ hU₀E
  have hb₁ : orderOf (piX Y A ⟨b, Subgroup.mem_sup_right hbA⟩) = 3 := by
    have h1 : (piX Y A ⟨b, Subgroup.mem_sup_right hbA⟩) =
        ((aEquiv (L := Y) hA ⟨b, hbA⟩ : aOne Y A) : QuotX Y A) := rfl
    rw [h1, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact orderOf_eq_prime (hAe.2 b hbA) hb1
  have hquad : Sec4.IsQuad417 (lOne Y A) (aOne Y A) ((E₀.subgroupOf (Y ⊔ A)).map (piX Y A))
      (piX Y A ⟨b, Subgroup.mem_sup_right hbA⟩) m :=
    ⟨maximal_aOne hAe hstd.mem_S.1.2.1,
      by rw [← Nat.card_congr (aEquiv (L := Y) hA).toEquiv, hm],
      aOne_inf_centralizer hA hAY hbA hCA, hb₁, hE₁, hE₁A, T, hT, hTc⟩
  have h417' := h417 (QuotX Y A) hX pCore_two_quotX (lOne Y A)
    (isComponent_lOne hAY Φ₀ hq) (quad_le_four h611 hstd.standing) (aOne Y A)
    ((E₀.subgroupOf (Y ⊔ A)).map (piX Y A)) (piX Y A ⟨b, Subgroup.mem_sup_right hbA⟩) m hquad
  exact list211_of_alt417 hAY hΦ₀ eAut eX hm h417'

end Item21Late2Proof

@[expose] def Item2130ONInspection : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (b : G)
    (U₀ Y : Subgroup G),
    Config2130 G A E U c L → Nat.card (A ⊓ L : Subgroup G) = 9 → Choice2130 A E c L b U₀ Y →
      A ≤ Y → List211 A b Y → Sec4.IsTripleCover (lBar Y) Blueprint.NativeSporadic.ON

@[expose] def Item2130TypesInspection : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (b : G)
    (U₀ Y : Subgroup G),
    Config2130 G A E U c L → Nat.card (A ⊓ L : Subgroup G) = 9 → Choice2130 A E c L b U₀ Y →
      ¬ A ≤ Y ⊔ Subgroup.zpowers b → List211 A b Y →
        c ∈ Y ∨ (c ∈ Y ⊔ Sec4.thetaQuotCentralizer Y ∧ ¬ A ≤ Y ⊔ Sec4.thetaQuotCentralizer Y)

theorem item2130LocalONType_of (h417 : Sec4.Item4_17) (h611 : Sec6.Item6_11_1)
    (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (h41 : Sec4.Item4_1LargePrime)
    (hIns : Item2130ONInspection) : Item2130LocalONType := by
  intro G _ _ A E U c L b U₀ Y hcfg h9 hC hAY
  exact hIns G A E U c L b U₀ Y hcfg h9 hC hAY
    (Item21Late2Proof.list211_of_mem_lZeroStarAt h417 h611 h45 h66 h41 hcfg.pair.toSec21Std
      hC.b_mem.1 hC.b_ne_one hC.y_mem).2

theorem item2130LocalTypes_of (h417 : Sec4.Item4_17) (h611 : Sec6.Item6_11_1)
    (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) (h41 : Sec4.Item4_1LargePrime)
    (hIns : Item2130TypesInspection) : Item2130LocalTypes := by
  intro G _ _ A E U c L b U₀ Y hcfg h9 hC hAY
  exact hIns G A E U c L b U₀ Y hcfg h9 hC hAY
    (Item21Late2Proof.list211_of_mem_lZeroStarAt h417 h611 h45 h66 h41 hcfg.pair.toSec21Std
      hC.b_mem.1 hC.b_ne_one hC.y_mem).2

end Certs

end CFSG.RankThree.PartTwo.Sec21
