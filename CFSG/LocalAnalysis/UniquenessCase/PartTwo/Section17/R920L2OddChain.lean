module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.R920L2OddThreeElts
public import CFSG.LocalAnalysis.UniquenessCase.Nine24R912L2
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R911
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R99
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R9R5
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09s

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

structure R920CfgL2 (D : Data G) (L D₃ A : Subgroup G) (n : ℕ) : Prop where
  mem : L ∈ calC D.M
  isL2 : IsL2 (Bar2 L) n
  odd : Odd n
  five_le : 5 ≤ n
  D₃_le : D₃ ≤ L
  D₃_card : Nat.card D₃ = 3
  D₃_mem : D₃ ∈ uniqueSet D.M
  A_le : A ≤ L
  A_prime : (Nat.card A).Prime
  A_dvd : Nat.card A ∣ 2 ^ n - 1
  A_mem : A ∈ uniqueSet D.M

theorem exists_chain_of_mem_calY2
    (h63c : CFSG.CGT.PushingUpLit.CGT6.AschbacherSixThreeCore) {D : Data G}
    (h640 : UC6.R6_40_1 D) {L D₃ A : Subgroup G} {n : ℕ} (c : R920CfgL2 D L D₃ A n)
    (hY2 : L ∈ F09.calY2_9 D) :
    ∃ Y H S : Subgroup G, L ≤ Y ∧ F09.Hyp97 D Y H D₃ S ∧ Opp 3 Y = L ∧
      IsSylowOf 2 S H ∧ IsSylowOf 2 S (H ⊓ D.M) ∧ (L.subgroupOf (H ⊓ D.M)).Normal := by
  obtain ⟨-, hLL, -⟩ :=
    normal_opp_eq_of_mem_calY2_of_calC' D c.mem c.isL2 hY2 le_rfl
  obtain ⟨Y, H, S, hLY, h97⟩ :=
    F09.exists_hyp97_of_mem_calY2_9 D hY2 (by rw [hLL]; exact c.D₃_le) c.D₃_card
  obtain ⟨-, hY, hR⟩ :=
    normal_opp_eq_of_mem_calY2_of_calC' D c.mem c.isL2 h97.2.1.prop hLY
  have h912 := F09.r912L2_of_inputs D (F09.r99_holds D) (F09.r910_holds D)
    (F09.r911_of h63c D h640) (F09.r9R5_holds D) Y H D₃ S h97 n
    (by have := c.five_le; omega) (hY ▸ c.isL2) hR
  have h5 := F09.r9R5_holds D Y H D₃ S h97
  exact ⟨Y, H, S, hLY, h97, hY, h912.1, h5.2, hY ▸ h5.1⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
