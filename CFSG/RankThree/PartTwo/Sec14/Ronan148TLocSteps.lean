module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TTheta
public import CFSG.RankThree.PartTwo.Sec14.Ronan148TLocPoint
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.SigHJ
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.SigM12
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.SigM22
public import CFSG.RankThree.PartTwo.Sec14.Item148ONLocProofCases
public import CFSG.RankThree.PartTwo.Sec14.Item148Res6ProofPGLNorm
public import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofSubfield
public import CFSG.RankThree.PartTwo.Sec14.Item148Res9Proof
public import CFSG.RankThree.PartTwo.Sec14.Item148ResProofEps
public import CFSG.RankThree.PartTwo.Sec14.Item148ResProofON
public import CFSG.RankThree.PartTwo.Sec14.Ronan148KOuter
public import CFSG.RankThree.PartTwo.Sec14.Ronan148KTyped
public import CFSG.RankThree.PartTwo.Sec14.Ronan148MAssembly

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14

theorem step148KTheta_of_loc
    (h429 : Sec4.Item4_29) (hKF : KF148SigL3Loc) : Step148KTheta := by
  obtain ⟨h45, h48, h41, -, h46, -, hGW, h131, -, -, -⟩ := Ronan148M.closedInputs
  exact Ronan148K.step148KTheta_of_typed h45 h48 h41 hGW
      (Ronan148K.kf148ThetaTyped_of h429
          CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)
      (step148KThetaHJ_of_sig CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.kf148SigHJ)
      (step148KThetaL3_of_loc h131 h46 h41 hKF)
      (step148KThetaA7_of_sig CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.kf148SigA7)
      (step148KThetaM22_of_sig CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.kf148SigM22)
      (step148KThetaM12_of_sig CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.kf148SigM12)
      step148KThetaON_holds

theorem step148KType_of_loc
    (hθ : Step148KTheta) (hKF : KF148SigL3Loc) : Step148KType := by
  obtain ⟨-, -, h41, -, h46, -, -, h131, -, -, -⟩ := Ronan148M.closedInputs
  exact step148KType_of_step148KTypeCover_holds
    (step148KTypeCover_of_theta hθ
      (step148KThetaOmega_of
        (step148KThetaHJ_of_sig CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.kf148SigHJ)
        (step148KThetaL3_of_loc h131 h46 h41 hKF)
        (step148KThetaA7_of_sig CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.kf148SigA7)
        (step148KThetaM22_of_sig CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.kf148SigM22)
        (step148KThetaM12_of_sig CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.kf148SigM12))
      (step148KThetaONCover_of_sigMax
        (kf148SigONMax_of_e27
          Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven.kf148SigONE27_holds)))

theorem steps148_of_leavesLoc
    (hKF : KF148SigL3Loc) (hEps : Item4_29EpsOuter)
    (h429 : Sec4.Item4_29) (hRF : Step148RankFive) (hCe : Step148PGLCent) :
    Step148KType ∧ Step148Lift429 ∧ Step148One ∧ Step148Rank ∧ Step148PGL := by
  obtain ⟨-, h48, h41, -, -, -, -, -, h134, h133, -⟩ := Ronan148M.closedInputs
  have hθ : Step148KTheta := step148KTheta_of_loc h429 hKF
  exact ⟨step148KType_of_loc hθ hKF, step148Lift429_of_item4_29EpsOuter h429 h41 hEps,
    step148One_holds, Item148Res8.step148Rank_of_res8_final h133 h134 h48 hRF,
    step148PGL_of (Item148Res6.step148PGLImg_of_cent hCe) step148PGLON_holds kf148PGLAbel
      kf148Inner kf148Field_holds⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
