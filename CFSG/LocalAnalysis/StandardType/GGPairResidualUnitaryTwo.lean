module

public import CFSG.LocalAnalysis.StandardType.GGMemberRowsDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoBridge
public import CFSG.RankThree.PartOne.TCB.SchreierFinal
public import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryTwoCell
public import CFSG.LocalAnalysis.StandardType.GGPairUnitaryTwoOdd
public import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryTwoSize
public import CFSG.LocalAnalysis.StandardType.GGMemberUnitaryTwoEven
public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceSchreier
public import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseTwoAFiveE
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGNsq2U62
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosAdapterAux

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Phan

theorem ggPairConcl_of_selected_unitary_two_exceptional
    (hTB : GGTBFixInput) (hP : GGStdSubPrimeInput) (hWA : GGTBFixNbrXInput)
    (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (𝒦 : Finset (Subgroup G))
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hL : ¬ GGSplitLie p L)
    (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (X : Subgroup G) (hX : X = L ∨ X ∈ 𝒦)
    (_hXs : ¬ GGSplitLie p X) (_hXu : ¬ GGMemberUnitary p Bs X)
    (hsel : GGInnerDiagOnLabel
      (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1 ∧ (lab.rank = 3 ∨ lab.rank = 5)) p Bs X)
    (r : MulAut ↥Bs) (hrA : r ∈ ggAutomizer X Bs) (hrC : r ∈ ggCoxRefl M e)
    (r' : MulAut ↥Bs) (hrA' : r' ∈ ggAutomizer X Bs) (hrC' : r' ∈ ggCoxRefl M e)
    (hne : r ≠ r') : GGPairConcl Bs X r r' := by
  classical
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hLB : GGLBalanceInput :=
    ggLBalanceInput_of_catalogueSchreier CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
  have hU : GGU62OuterDiagInput := ggU62OuterDiagInput_holds
  have hT : GGSecFiveE6QTwoTimmesfeldInput := ggSecFiveE6QTwoTimmesfeldInput_holds
  have hr : GGIsReflection p r := ggCoxRefl_isReflection hpres.2 hrC
  have hr' : GGIsReflection p r' := ggCoxRefl_isReflection hpres.2 hrC'
  by_cases hodd : Odd (Nat.card (Subgroup.center ↥X))
  · exact ggPairConcl_of_esu_two_odd hcfg hX hodd hsel hrA hrA' hr hr' hne
  · have h5 := ggMember_unitaryTwoCell_rank_five hLB hP hcfg hX hsel
    have hBB : B = Bs := by
      by_contra hne'
      exact hodd (GGConfig.odd_card_center_of_innerDiagOnLabel hcfg.1.1
        (lt_of_le_of_ne hcfg.1.1.2.1.1 hne') h5)
    have hp3 : p = 3 := by
      obtain ⟨hp, -, -, -, -⟩ := hcfg.1.1.tableB_facts
      obtain ⟨-, lab, -, hraw⟩ := h5
      obtain ⟨R, _, I, F, -, -, θ, hP⟩ := largeEvenRawDatum_exists hraw
      obtain ⟨⟨hrow, hn1, -⟩, -, -⟩ := hP
      refine (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp ?_
      have h := hrow.2
      rw [hn1] at h
      norm_num at h
      exact h
    subst hp3
    rcases hX with hXL | hX
    · subst hXL
      by_cases hAD : GGIsWeylMatrixA M ∨ NSJoin.NSTypeD M
      · have hcent := ggNSPosPD_routeCfg_cent_L hcfg.1.1
        have h3pow := ggL_three_pow_six_of_card_automizer hTB hWA hcfg hpres hAD h5
        exact ggPairConcl_of_twA5_two_even hU hcfg hBB hcent h5 h3pow hrA hrA' hr hr' hne
      · rw [not_or] at hAD
        have hE : GGIsWeylMatrixE M :=
          GGIsWeylMatrixE.of_not_typeA_not_typeD hpres.1 hle3 hAD.1 hAD.2
        have hlt := GGSecFiveRouteCfg.lt_bstar_of_twA5_typeE hT hTB hU hcfg hpres hE hL h5
        exact absurd hBB (ne_of_lt hlt)
    · obtain ⟨y, hnbr⟩ := hcfg.2.2.2.1.2 X hX
      have hcent := ggNSPosPD_routeCfg_cent_K Nat.prime_three hnbr
      have h3pow := ggMember_three_pow_six_of_card_automizer hRig hLB hP hTB hcfg hpres hle3
        hBB hX h5
      exact ggPairConcl_of_twA5_two_even hU hcfg hBB hcent h5 h3pow hrA hrA' hr hr' hne

end CFSG.StandardType

end
