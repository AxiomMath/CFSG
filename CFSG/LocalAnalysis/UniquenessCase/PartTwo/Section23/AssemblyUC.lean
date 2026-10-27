module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Assembly
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.FourHX
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.Holds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC

theorem tiStage1930_of_s23InputsUC (hE : UC22P20gExcFacts)
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (hC : ∀ (G : Type) [Group G] [Finite G], Standing G → AGL81TheoremC G)
    (h846 : ∀ (G : Type) [Group G] [Finite G] (hS : Standing G), rankThreeUC G →
      AGL81TheoremC G → ∀ S : Setup G, S.InMSigma →
        F08.R846 (PartTwo.Three.dataOfSetup hS S))
    (h899 : ∀ (G : Type) [Group G] [Finite G] (hS : Standing G), rankThreeUC G →
      ∀ S : Setup G, S.InMSigma → (∀ H ∈ hSet S.T S.M, Asc1930 S.M H) →
        CFSG.CGT.Timmesfeld75.IsTI (uCore S.M S.T) →
          F08.R899 (PartTwo.Three.dataOfSetup hS S))
    (h : ∀ (G : Type) [Group G] [Finite G] (hS : Standing G), rankThreeUC G →
      AGL81TheoremC G → ∀ S : Setup G, S.InMSigma → (∀ H ∈ hSet S.T S.M, Asc1930 S.M H) →
        CFSG.CGT.Timmesfeld75.IsTI (uCore S.M S.T) →
          ∃ Ch : Choice2011 G, S23Inputs (PartTwo.Three.dataOfSetup hS S) Ch ∧
            S21_8N (PartTwo.Three.dataOfSetup hS S) Ch ∧
              S21_21B (PartTwo.Three.dataOfSetup hS S) Ch) :
    CFSG.Yardstones.Me2c15c2c995a.AscSectionTwentyThree := by
  intro G _ _ hS hUC S hMS h1930 hTI
  obtain ⟨Ch, I, h218, h2121⟩ := h G hS hUC (hC G hS) S hMS h1930 hTI
  exact false_of_s23Inputs hE hSch S.notCatalog (PartTwo.Three.dataOfSetup hS S) Ch
    h1930 (by simpa [PartTwo.Three.dataOfSetup] using (dataExt_ofSetup hS S).hne)
    hTI (UC6S846.sigmaStd_dataOfSetup hS S) (PartTwo.Three.r6_1_dataOfSetup hS S)
    (sigma23Std_ofSetup hS S) (uc22p22c_hyp612_of_sigma2 hS S)
    (UC6.r6_11Used_dataOfSetup hS S) (h846 G hS hUC (hC G hS) S hMS)
    (h899 G hS hUC S hMS h1930 hTI) h218 h2121 hS.rank I

theorem tiParts1930_of_s23InputsUC (hE : UC22P20gExcFacts)
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (hC : ∀ (G : Type) [Group G] [Finite G], Standing G → AGL81TheoremC G)
    (h846 : ∀ (G : Type) [Group G] [Finite G] (hS : Standing G), rankThreeUC G →
      AGL81TheoremC G → ∀ S : Setup G, S.InMSigma →
        F08.R846 (PartTwo.Three.dataOfSetup hS S))
    (h899 : ∀ (G : Type) [Group G] [Finite G] (hS : Standing G), rankThreeUC G →
      ∀ S : Setup G, S.InMSigma → (∀ H ∈ hSet S.T S.M, Asc1930 S.M H) →
        CFSG.CGT.Timmesfeld75.IsTI (uCore S.M S.T) →
          F08.R899 (PartTwo.Three.dataOfSetup hS S))
    (h : ∀ (G : Type) [Group G] [Finite G] (hS : Standing G), rankThreeUC G →
      AGL81TheoremC G → ∀ S : Setup G, S.InMSigma → (∀ H ∈ hSet S.T S.M, Asc1930 S.M H) →
        CFSG.CGT.Timmesfeld75.IsTI (uCore S.M S.T) →
          ∃ Ch : Choice2011 G, S23Inputs (PartTwo.Three.dataOfSetup hS S) Ch ∧
            S21_8N (PartTwo.Three.dataOfSetup hS S) Ch ∧
              S21_21B (PartTwo.Three.dataOfSetup hS S) Ch) :
    ∀ (G : Type) [Group G] [Finite G], Standing G →
      TIUCoreEq1930 G ∧ TIUNoncyclic G ∧ TIStageNotClauseC1930 G := by
  intro G _ _ hS
  refine ⟨?_, ?_, ?_⟩
  · intro hUC S hMS h1930 hTI
    let D : Data G := PartTwo.Three.dataOfSetup hS S
    obtain ⟨Ch, I0, -⟩ := h G hS hUC (hC G hS) S hMS h1930 hTI
    have I : S23Inputs D Ch := I0
    have hH : (hSet D.T D.M).Nonempty := by
      simpa [D, PartTwo.Three.dataOfSetup] using S.hSet_nonempty
    obtain ⟨c, -⟩ := exists_ctx23L_of_s23Inputs D Ch h1930 hH hTI I.toS23InputsCore
    have h4 : S23_4 D Ch :=
      s23_4_of_inputN D Ch (I.s23_4_input hE S.notCatalog) I.fusion I.s20_4 I.s20_8 I.s20_10
        I.choice
    have hUZ : D.U = D.Z := (h4 h1930 c).1
    simpa [D, PartTwo.Three.dataOfSetup, Data.U, Data.Z] using hUZ
  · intro hUC S hMS h1930 hTI hcyc
    let D : Data G := PartTwo.Three.dataOfSetup hS S
    obtain ⟨Ch, I0, -⟩ := h G hS hUC (hC G hS) S hMS h1930 hTI
    have I : S23Inputs D Ch := I0
    have hH : (hSet D.T D.M).Nonempty := by
      simpa [D, PartTwo.Three.dataOfSetup] using S.hSet_nonempty
    obtain ⟨c, -⟩ := exists_ctx23L_of_s23Inputs D Ch h1930 hH hTI I.toS23InputsCore
    have h4 : S23_4 D Ch :=
      s23_4_of_inputN D Ch (I.s23_4_input hE S.notCatalog) I.fusion I.s20_4 I.s20_8 I.s20_10
        I.choice
    have h2 := I.s23_2_natural_of_core hE
    have h3 := I.s23_3_of_core hE S.notCatalog
    have hline : S23_5_line D Ch :=
      s23_5_line_of D Ch h2 h3 h4 I.s20_9 KOrdNat.kOrdNatural_holds
        kTab23a_holds kTab23b_holds kTab23c_holds kSchurL2_holds
    have h52 : S23_5_2 D Ch := s23_5_2_of D Ch hline kNshape_holds
    have hUZ : D.U = D.Z := (h4 h1930 c).1
    have hn3 : 3 ≤ c.n := uc22p20g_hn3_of hE D Ch I.s20_7 h1930 c.toCtx23.toCtx21
    have hn : 2 ≤ CFSG.Open.pRank 2 D.Z := by
      rcases h52 h1930 c with hh | ⟨-, -, hh⟩
      · rw [hh] at hn3
        omega
      · rw [hh] at hn3
        omega
    have hUZ' : uCore S.M S.T = CFSG.RankThree.PartOne.omegaOneCenterIn S.T := by
      simpa [D, PartTwo.Three.dataOfSetup, Data.U, Data.Z] using hUZ
    have hn' : 2 ≤ CFSG.Open.pRank 2 (CFSG.RankThree.PartOne.omegaOneCenterIn S.T) := by
      simpa [D, PartTwo.Three.dataOfSetup, Data.Z] using hn
    have h1 : CFSG.Open.pRank 2 (uCore S.M S.T) ≤ 1 :=
      CFSG.SectionRank.pRank_le_one_of_isCyclic Nat.prime_two hcyc
    rw [hUZ'] at h1
    omega
  · intro hUC S hMS h1930 hTI _
    exact tiStage1930_of_s23InputsUC hE hSch hC h846 h899 h G hS hUC S hMS h1930 hTI

end CFSG.LocalAnalysis.UniquenessCase.UC22
