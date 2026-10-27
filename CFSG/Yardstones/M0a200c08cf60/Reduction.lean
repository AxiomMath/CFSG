module

public import CFSG.Yardstones.Statements.Yd9d0461841b24864
public import CFSG.Yardstones.Statements.Yb5567054060d2637
public import CFSG.Yardstones.Statements.Y3d4b421cf453ec64
public import CFSG.Yardstones.Statements.Y59ee199fc9bc58d0
public import CFSG.Yardstones.Statements.Y6903dedceba0002d
public import CFSG.Yardstones.Statements.Y4bf4f8795e8c7fff
public import CFSG.Yardstones.Statements.Yb031d16c41bb4bea
public import CFSG.Yardstones.Statements.Y0d140413618caf8e
public import CFSG.Yardstones.Statements.Y65d04821f0bd29bc
public import CFSG.Yardstones.Statements.Yff9f051bd0f2e3a6
public import CFSG.Yardstones.Statements.Yccd030af2915bf0b
public import CFSG.Yardstones.Statements.Y4ff32cfc4805739b
public import CFSG.Yardstones.Statements.Y9acdb75f78146540
public import CFSG.Yardstones.Statements.Y8a9c30e4e7d2630f
public import CFSG.Yardstones.Statements.Y5283f3453716220f
public import CFSG.LocalAnalysis.AGLEmbedding.D1AssemblyIII
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharNonNormalLinear
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.ExcE
public import CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.D1EightTen
public import CFSG.HardMathSupport.Foote.Coordinator.CoverThree.Final
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.Final
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.ReeF4Three
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieFinal
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieNeg
public import CFSG.HardMathSupport.Lang.TwE6Step3.CubesV4
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.ResidualHandback
public import CFSG.HardMathSupport.Lang.AnisoF4.FinalEven
public import CFSG.HardMathSupport.Lang.AnisoE8.Final
public import CFSG.HardMathSupport.Lang.AnisoE6.TwFinal
public import CFSG.LieType.SeitzGeneration.ExcAnisotropicAssemblyV6

public section

namespace CFSG.Yardstones.M0a200c08cf60


open CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator
  CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
  CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner
  CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower in
theorem lc_gl_embedding_theorem_d1_rank_four_of_yardstones
    (h01 : CFSG.Yardstones.Statements.Yd9d0461841b24864)
    (h02 : CFSG.Yardstones.Statements.Yb5567054060d2637)
    (h03 : CFSG.Yardstones.Statements.Y3d4b421cf453ec64)
    (h04 : CFSG.Yardstones.Statements.Y59ee199fc9bc58d0)
    (h05 : CFSG.Yardstones.Statements.Y6903dedceba0002d)
    (h06 : CFSG.Yardstones.Statements.Y4bf4f8795e8c7fff)
    (h07 : CFSG.Yardstones.Statements.Yb031d16c41bb4bea)
    (h08 : CFSG.Yardstones.Statements.Y0d140413618caf8e)
    (h09 : CFSG.Yardstones.Statements.Y65d04821f0bd29bc)
    (h10 : CFSG.Yardstones.Statements.Yff9f051bd0f2e3a6)
    (h11 : CFSG.Yardstones.Statements.Yccd030af2915bf0b)
    (h12 : CFSG.Yardstones.Statements.Y4ff32cfc4805739b)
    (h13 : CFSG.Yardstones.Statements.Y9acdb75f78146540)
    (h14 : CFSG.Yardstones.Statements.Y8a9c30e4e7d2630f)
    (h15 : CFSG.Yardstones.Statements.Y5283f3453716220f)
    (hCIT : CFSG.ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Open.IsKProper G) (hchar : CFSG.Open.IsCharTwoType G)
    (he : 4 ≤ CFSG.Open.evenRank G) (hpre : CFSG.Open.GLBPreuniqueness G)
    (p : ℕ) (hp : p ∈ CFSG.Open.GLBBetaFour G) (P : Sylow p G)
    (M : Subgroup G) (hM : CFSG.Open.GLBIsMaxTwoLocal M)
    (hWM : CFSG.Open.GLBWeakCore p (P : Subgroup G) ≤ M)
    (H : Subgroup G) (hH : CFSG.Open.IsTwoLocal H) (hHM : 3 ≤ CFSG.Open.pRank p (H ⊓ M)) :
    H ≤ M := by
  have y01 : TwistedE6TypeBound := h01
  have y02 : CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.OrthMinusCentOb := h02
  have y03 : CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0NonShortNotCaseIStatement :=
    h03
  have y04 : ExcAnisotropicF4Residuals := h04
  have y05 : ExcAnisotropicE6E8Residuals := h05
  have y06 : ExcAnisotropicThreeResiduals := h06
  have y07 : CFSG.LieType.SeitzGeneration.SubfieldPairOmegaPlusF2 := h07
  have y08 : CFSG.LieType.SeitzGeneration.SubfieldPairOmegaMinusF2 := h08
  have y09 : ExcOuterLeOneResiduals := h09
  have y10 : CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.SubfieldPairReeG2 := h10
  have y11 : TrialityPhi6Placements := h11
  have y12 : CFSG.AGLEmbedding.KFactSeitzOuterCubeRankTwo := h12
  have y13 : P1OffCharNonNormalRest := h13
  have y14 : CFSG.ClassicalInvolution.Q3.CIT3Inductive := h14
  have y15 : CFSG.CGT.PushingUpLit.SolKNA.TightLiftSimple := h15
  obtain ⟨h810, h93⟩ :=
    CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.d1EightTenNineThree_of_three y01 y02
      (CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.e0NonShortNotHYcStatement_of_caseI y03)
  have hW : ∀ r : ℕ, 5 ≤ r → CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6CoreW r :=
    fun r hr => CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.phi6CoreW_of_placementSome hr
      (y11.ge5 r hr) (y11.three r hr)
  have hAniN :
      CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.SeitzExcAnisotropicNotG2ThreePlus :=
    CFSG.LieType.SeitzGeneration.seitzExcAnisotropicNotG2ThreePlus_of_residualsV6
      { g2NineFive :=
          CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.seitzExcAnisotropicG2NineFive_proved
        g2Three := seitzExcAnisotropicG2ThreeMinus_proved
        trialityOdd := seitzExcAnisotropicTrialityOdd_of_coreW hW
        trialityThree := y06.trialityThree
        f4Phi3 := y04.f4Phi3
        f4Phi4 := CFSG.HardMathSupport.Lang.AnisoF4.seitzExcAnisotropicF4Class_four
        f4Phi6 := y04.f4Phi6
        e6Phi6 := y05.e6Phi6
        e8Phi5 := y05.e8Phi5
        e8Phi8 := CFSG.HardMathSupport.Lang.AnisoE8.seitzExcAnisotropicE8Class_eight
        e8Phi10 := y05.e8Phi10
        e8Phi12 := y05.e8Phi12
        twE6Phi3 :=
          CFSG.HardMathSupport.Lang.AnisoE6.seitzExcAnisotropicTwistedE6Class_three_of_f4 y04.f4Phi3
        twE6Phi4 := CFSG.HardMathSupport.Lang.AnisoF4.seitzExcAnisotropicTwistedE6Class_four
        reeF4Three := y06.reeF4Three }
  have hXC : CFSG.AGLEmbedding.SeitzCyc.SeitzExcOuterCycResiduals :=
    ⟨y09.f4LeOne, y09.e6LeOne, y09.e7LeOne, y09.e8LeOne, y09.twistedE6LeOne,
      CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.seitzExcOuterNarrowReeG2_of_pair y10,
      CFSG.LieType.SeitzGeneration.seitzExcOuterNarrowReeF4Three_holds⟩
  have hGA := CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  have hNN : CFSG.AGLEmbedding.P1OffCharAlmostSimpleNonNormal :=
    CFSG.AGLEmbedding.p1OffCharAlmostSimpleNonNormal_of_at fun ⟨d, hv⟩ => by
      by_cases hA : ∃ (m : ℕ) (q : TauCeti.PrimePower), d = .A m q
      · obtain ⟨m, q, rfl⟩ := hA
        exact CFSG.AGLEmbedding.p1OffCharAlmostSimpleNonNormalAt_A_all hv
      by_cases h6 : ∃ q : TauCeti.PrimePower, d = .E6 q
      · obtain ⟨q, rfl⟩ := h6
        exact p1OffCharAlmostSimpleNonNormalAt_E6 hv
      by_cases h7 : ∃ q : TauCeti.PrimePower, d = .E7 q
      · obtain ⟨q, rfl⟩ := h7
        exact p1OffCharAlmostSimpleNonNormalAt_E7 hv
      exact y13 ⟨d, hv⟩ (fun m q h => hA ⟨m, q, h⟩) (fun q h => h6 ⟨q, h⟩) (fun q h => h7 ⟨q, h⟩)
  have hP1Off : CFSG.AGLEmbedding.P1ThreeLieOffChar :=
    CFSG.AGLEmbedding.p1ThreeLieOffChar_of_cubesV10
      (CFSG.HardMathSupport.Lang.TwE6Step3.excCubeResidualsV4_of_phi6 fun r hr =>
        CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.phiPlaneGenAt_neg_of_coreW hr (hW r hr))
      hGA (CFSG.HardMathSupport.Foote.Coordinator.p1OffCharCoverThree hGA)
      (p1OffCharCoverThreeNoInner_holds hGA)
      y12 hNN
  have hQL : CFSG.CGT.PushingUpLit.SolKNA.QuaternionInspectionLie :=
    CFSG.CGT.PushingUpLit.SolKNA.quaternionInspectionLie_of_cit3_neg
      CFSG.CGT.PushingUpLit.SolKNA.neg3Table_holds y14 y15
  exact CFSG.AGLEmbedding.d1_of_obligations h810 hAniN y07 y08 hXC hP1Off hCIT hQL h93
    G hnonab hK hchar he hpre p hp P M hM hWM H hH hHM

end CFSG.Yardstones.M0a200c08cf60
