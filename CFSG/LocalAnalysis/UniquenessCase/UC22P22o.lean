module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Main7
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22n
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22nA
public import CFSG.LocalAnalysis.RankThreeUC.TIModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.CGT.Timmesfeld75 (IsTI)

variable {G : Type} [Group G] [Finite G]

theorem uc22p22o_inCalW_U_of_not_isTI (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (hU : ¬ IsTI D.U) : InCalW D.M D.T D.U :=
  ⟨uc22p22n_inCalV1_of_not_isTI D hx h61 (uc22p22e_inCalV_U D) hU,
    uc22p22n_eight_le_card D hx h61 (uc22p22e_inCalV_U D) hU,
    uc22p22na_twoReduced_iSup_conj D.sylowM
      ((omegaOneCenterIn_le_inf_centralizer D.T).trans inf_le_right)⟩

theorem uc22p22o_s22_1_derived (D : Data G) (Ch : Choice2011 G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h111 : F11.R111 D) (h112 : F11.R112 D) : S22_1 D Ch :=
  s22_1_of D Ch h111 h112 fun _ c => uc22p22o_inCalW_U_of_not_isTI D hx h61 c.hU

theorem uc22p22o_inCalV_of_le_U (D : Data G) {V : Subgroup G} (hVU : V ≤ D.U) (hVne : V ≠ ⊥)
    (hVM : D.M ≤ normalizer (V : Set G)) : InCalV D.M V :=
  ⟨hVne, hVU.trans (uc22p22e_uCore_le D.sylowM.le), hVM,
    uc22p22n_isElemAbelian_of_le hVU (uc22p22e_inCalV_U D).2.2.2⟩

theorem uc22p22o_not_isTI_of_hC (D : Data G) {V : Subgroup G} (hV : InCalV D.M V)
    (hC : ¬ centralizer (D.Z : Set G) ≤ D.M) : ¬ IsTI V := by
  intro hTI
  have hTN : D.T ≤ normalizer (V : Set G) := D.sylowM.le.trans hV.2.2.1
  obtain ⟨z, hz, hz1⟩ := Subgroup.exists_mem_ne_one_of_ne_bot
    (uc22p22na_inf_center_ne_bot D.sylowM.isPGroup (uc22p22na_le_T_of_inCalV D hV) hTN hV.1)
  have hzZ : z ∈ D.Z := by
    refine CFSG.RankThree.PartOne.Sec15Final.mem_omegaOneCenterIn_iff.2
      ⟨hz.2.1, fun k hk => ?_, ?_⟩
    · exact Subgroup.mem_centralizer_iff.mp hz.2.2 k hk
    · exact hV.2.2.2.2 z hz.1
  apply hC
  exact (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hzZ)).trans
    (centralizer_le_of_isTI D.maxLocal hV.1 (uc22p22e_isPGroup_of_elem hV.2.2.2) hV.2.2.1 hTI
      hz.1 hz1)

theorem uc22p22o_s22_V_derived (D : Data G) (Ch : Choice2011 G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) : S22_V D Ch := by
  intro _ c
  have hV : InCalV D.M c.V := uc22p22o_inCalV_of_le_U D c.hVU c.hVne c.hVM
  have hTI : ¬ IsTI c.V := uc22p22o_not_isTI_of_hC D hV c.hC
  exact ⟨⟨uc22p22n_inCalV1_of_not_isTI D hx h61 hV hTI, uc22p22n_eight_le_card D hx h61 hV hTI,
    uc22p22na_twoReduced_of_irr D hV c.hVirr⟩, fun p hp =>
    ⟨uc22p22n_one_lt_pRank_mbar D hx h61 hV hTI p hp,
      uc22p22n_pRank_centralizer_le_one D h61 hV hTI p hp⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
