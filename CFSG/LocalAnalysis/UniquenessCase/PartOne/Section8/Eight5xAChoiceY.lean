module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight5xAShared
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight67Subnormal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open scoped commutatorElement
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

theorem ChoiceY.not_normalizer_le_of_le {G : Type} [Group G] [Finite G] {D : Data G}
    {L Q P X Y : Subgroup G} (h862 : R862 D) (hY : ChoiceY D L Q P X Y) {Z : Subgroup G}
    (hZY : Z ≤ Y) : ¬ Subgroup.normalizer (Z : Set G) ≤ D.M := by
  intro hN
  have hcex := hY.cx.cex
  have hU : Z ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M :=
    (h862 L Q P hcex).2 Z (hZY.trans hY.YP) hN
  have hY3 : IsPGroup 3 Y := hcex.sylowP.isPGroup.to_le hY.YP
  have hsub : IsSubnormal Z Y :=
    (IsSubnormal.iff_subgroupOf hZY).mpr
      (BaerSuzuki.Helpers.subgroup_isSubnormal_of_isPGroup (G := ↥Y) hY3 (Z.subgroupOf Y))
  exact false_of_subnormal_InU_of_not_normalizer_le
    (CFSG.LocalAnalysis.UniquenessCase.UC6.normalizer_eq_of_isMaxTwoLocal D.maxLocal) hsub
    (CFSG.LocalAnalysis.UniquenessCase.PartTwo.inU_iff_mem_uniqueSet.2 hU) hY.notLe

theorem ChoiceY.inf_eq_bot {G : Type} [Group G] [Finite G] {D : Data G}
    {L Q P X Y : Subgroup G} (h862 : R862 D) (hY : ChoiceY D L Q P X Y) : Y ⊓ Q = ⊥ := by
  by_contra hne
  have hcex := hY.cx.cex
  have hK3 : IsPGroup 3 (Y ⊓ Q : Subgroup G) := hcex.sylowQ.isPGroup.to_le inf_le_right
  have : Nontrivial ↥(Y ⊓ Q) := (Subgroup.nontrivial_iff_ne_bot (Y ⊓ Q)).mpr hne
  obtain ⟨g, hg⟩ := exists_ne (1 : ↥(Y ⊓ Q))
  have h3dvd : 3 ∣ Nat.card (Y ⊓ Q : Subgroup G) :=
    (hK3.dvd_orderOf hg).trans (orderOf_dvd_natCard g)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Y ⊓ Q)) 3 h3dvd
  have hx3 : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  have hY₀Q : Subgroup.zpowers (x : G) ≤ Q := Subgroup.zpowers_le.mpr x.2.2
  have hY₀Y : Subgroup.zpowers (x : G) ≤ Y := Subgroup.zpowers_le.mpr x.2.1
  have hY₀card : Nat.card (Subgroup.zpowers (x : G)) = 3 := by rw [Nat.card_zpowers, hx3]
  exact ChoiceY.not_normalizer_le_of_le h862 hY hY₀Y
    (normalizer_le_of_card_three_of_gamma hcex.gamma hY₀Q hY₀card)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
