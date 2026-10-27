module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148SH2Rows
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SCenter

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Ronan148S

variable {Γ : Type} [Group Γ] [Finite Γ]

section Center


theorem rowOfH2_of_center {X : Type} [Group X]
    (hZS : ∀ (L : Type) [Group L] [Finite L], SectionFourHyp L → IsQuasisimple L →
      IsPGroup 3 (Subgroup.center L) → Nonempty (L ⧸ Subgroup.center L ≃* X) →
      Subgroup.center L = ⊥)
    (hconcl : ∀ (L : Type) [Group L], Nonempty (L ≃* X) → ConclH2 L) : RowOfH2 X := by
  intro S _ _ _ _ ⟨eSX⟩ Γ _ _ C hC4 hCθ _ A L K d _ hLA _ _ _ hLq hCL _ _ _ _ _ _ ⟨e⟩ _
  have hLC : L ≤ C := hLA ▸ le_sup_left
  have hSL : SectionFourHyp ↥L :=
    Census.sectionFourHyp_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLC)
      (sectionFourHyp_subgroup hC4 (L.subgroupOf C))
  have hZ := hZS ↥L hSL hLq (isPGroup_center_of_normal hCθ hLC hCL hLq) ⟨e.trans eSX⟩
  exact hconcl ↥L ⟨((RonanK429.quotCenterEquivOfEqBot hZ).trans e).trans eSX⟩

end Center

section Rows



theorem checkSL_m24 : ∀ q < 626, 2 ≤ q → q ^ 3 ∣ 244823040 →
    244823040 * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  decide +kernel

theorem checkSU_m24 : ∀ q < 626, 2 ≤ q → q ^ 3 ∣ 244823040 →
    244823040 * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  decide +kernel

theorem rowOfH2_j2 : RowOfH2 (Spor .J2) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.J2 ≃* Spor .J2 := b
  refine rowOfH2_of_center (fun L _ _ hS hL hZ3 ⟨e⟩ => ?_) fun L _ ⟨e⟩ => Or.inl ⟨e.trans b'.symm⟩
  have hc : Nat.card (L ⧸ Subgroup.center L) = 604800 := by
    rw [Nat.card_congr (e.trans b'.symm).toEquiv, KFacts.KS14.card_nativeJ2]
  exact center_eq_bot_of_card hS hL hZ3 (N := 604800) hc
    (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSL_j2)
    (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSU_j2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem rowOfH2_m24 :
    RowOfH2 (Spor .M24) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.M24 ≃* Spor .M24 := b
  refine rowOfH2_of_center (fun L _ _ hS hL hZ3 ⟨e⟩ => ?_)
    fun L _ ⟨e⟩ => Or.inr (Or.inl ⟨e.trans b'.symm⟩)
  have hc : Nat.card (L ⧸ Subgroup.center L) = 244823040 := by
    rw [Nat.card_congr (e.trans b'.symm).toEquiv, CFSG.Sporadic.Mathieu.card_M24]
  exact center_eq_bot_of_card hS hL hZ3 (N := 244823040) hc
    (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSL_m24)
    (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSU_m24)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Rows

end CFSG.RankThree.PartTwo.Sec14.Ronan148S
