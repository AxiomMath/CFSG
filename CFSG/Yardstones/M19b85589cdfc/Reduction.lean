module

public import CFSG.Yardstones.Statements.Ya6ee879e9e00e1c6
public import CFSG.Yardstones.Statements.Y4d82408ed14bc230
public import CFSG.Yardstones.Statements.Y7462aa054ad6fb69
public import CFSG.Yardstones.Statements.Y71c65a150c2386bc
public import CFSG.Yardstones.Statements.Y3e8889d74d6732aa
public import CFSG.Yardstones.Statements.Y041a17812e904778
public import CFSG.Yardstones.Statements.Y85330bd65dba49a1
public import CFSG.Yardstones.Statements.Yd566e4b7a1078b04
public import CFSG.Yardstones.Statements.Y5f6198ef1a22ebc7
public import CFSG.Yardstones.Statements.Y104ce68084dd8482
public import CFSG.Yardstones.Statements.Y01a8ebe3a78892bf
public import CFSG.LocalAnalysis.AGLEmbeddingD2.MilestoneFrontierTight
public import CFSG.HardMathSupport.Malle.SeitzCube.InnerExFrontier
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.FrontierSeitz
public import CFSG.LieType.SeitzGeneration.ConsumerEx
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.AssemblyGraph
public import CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.SharedFrontier
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.Closed
public import CFSG.LieType.SeitzGeneration.SpF2.Main
public import CFSG.HardMathSupport.Malle.Coordinator.SubfieldPairs.SUOddTwoBig
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.RankOneA1Case
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusU3
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.ResidualsV5

public section

namespace CFSG.Yardstones.M19b85589cdfc

open CFSG.Open

theorem gls3PlusRankOneCharThree_of_reeG2 (hRee : Gls3PlusReeG2) :
    ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 3 →
      CFSG.AGLEmbedding.IsRankOneLieIndex d.1 →
        CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3PlusCase (.lie d) := by
  intro d h3 hr
  rcases hr with ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨m, hm⟩
  · rw [hq, TauCeti.LieTypeIndex.characteristic_A] at h3
    exact CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.gls3PlusCase_lie_rankOne_A1
      q h3 d hq
  · rw [hq, TauCeti.LieTypeIndex.characteristic_twistedA] at h3
    exact CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.gls3PlusCase_lie_rankOne_U3 q h3 d hq
  · exact hRee d m hm


theorem lc_gl_embedding_theorem_d2_rank_four_of_yardstones
    (hD1 : D1RankFourStatement)
    (hCIT : CFSG.ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (h01 : CFSG.Yardstones.Statements.Ya6ee879e9e00e1c6)
    (h02 : CFSG.Yardstones.Statements.Y4d82408ed14bc230)
    (h03 : CFSG.Yardstones.Statements.Y7462aa054ad6fb69)
    (h04 : CFSG.Yardstones.Statements.Y71c65a150c2386bc)
    (h05 : CFSG.Yardstones.Statements.Y3e8889d74d6732aa)
    (h06 : CFSG.Yardstones.Statements.Y041a17812e904778)
    (h07 : CFSG.Yardstones.Statements.Y85330bd65dba49a1)
    (h08 : CFSG.Yardstones.Statements.Yd566e4b7a1078b04)
    (h09 : CFSG.Yardstones.Statements.Y5f6198ef1a22ebc7)
    (h10 : CFSG.Yardstones.Statements.Y104ce68084dd8482)
    (h11 : CFSG.Yardstones.Statements.Y01a8ebe3a78892bf)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Open.IsKProper G) (hchar : CFSG.Open.IsCharTwoType G)
    (he : 4 ≤ CFSG.Open.evenRank G)
    (hδ₁ : CFSG.Open.GLBDeltaOne G) (hδ₂ : CFSG.Open.GLBDeltaTwo G)
    (p : ℕ) (hp : p ∈ CFSG.Open.GLBBetaFour G) (P : Sylow p G)
    (M : Subgroup G) (hM : CFSG.Open.GLBIsMaxTwoLocal M)
    (hPM : CFSG.Open.GLBCore p 2 (P : Subgroup G) ≤ M)
    (Q : Subgroup G) (hQ : IsPGroup p Q) (hQrank : CFSG.Open.pRank p Q = 2)
    (hQM : CFSG.Open.GLBCore p 1 Q ≤ M)
    (H : Subgroup G) (hH : CFSG.Open.IsTwoLocal H) (hQH : Q ≤ H) :
    H ≤ M := by
  have y01 : CFSG.LieType.SeitzGeneration.SubfieldPairOmegaPlusF2 := h01
  have y02 : CFSG.LieType.SeitzGeneration.SubfieldPairOmegaMinusF2 := h02
  have y03 :
      CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.SeitzExcAnisotropicNotG2ThreePlus :=
    h03
  have y04 : CFSG.AGLEmbedding.SeitzCyc.SeitzExcOuterCycResiduals := h04
  have y05 : Gls3PlusReeG2 := h05
  have y06 : CFSG.AGLEmbeddingD2.Tits.GN516.KFactChevGraphOrbit := h06
  have y07 : CFSG.AGLEmbeddingD2.Tits.GN516.AGL81I516SymOver := h07
  have y08 : TwistedE6TypeBound := h08
  have y09 : CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.OrthMinusCentOb := h09
  have y10 : CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0NonShortNotCaseIStatement := h10
  have y11 : CFSG.CGT.PushingUpLit.SolKNA.QuaternionInspectionLie := h11
  have hIL := CFSG.HardMathSupport.Malle.SeitzCube.innerEx_lowN_of_pairs_aniso
    CFSG.LieType.SeitzGeneration.subfieldPairSpF2_holds
    CFSG.HardMathSupport.Malle.Coordinator.SubfieldPairs.subfieldPairSUOddTwo_holds
    (CFSG.LieType.SeitzGeneration.subfieldPairOmegaPlusChar2_of_F2 y01)
    (CFSG.LieType.SeitzGeneration.subfieldPairOmegaMinusChar2_of_F2 y02) y03
    (CFSG.LieType.SeitzGeneration.seitzExcOuterNarrow_of_residualsV5
      (CFSG.AGLEmbedding.SeitzCyc.SeitzExcOuterCycResiduals.toV5 y04))
  have hsh := CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.sharedD2Inputs_of_three y08 y09
    (CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.e0NonShortNotHYcStatement_of_caseI y10)
  have hE0n := CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.e0NotYStatement_of_nonshort
    hsh.2.2
  have hFO := CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.eightTenNodeFourOrbit_of_E0
    CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.e0Statement_proved hE0n
  have hCF := CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.eightTenNodeColourFour_of_E0
    CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.e0Statement_proved hE0n
  have hGLSPlus :=
    CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.gls3StronglyThreeEmbeddedPlus_of_seitz
      (CFSG.LieType.SeitzGeneration.offCharGen_of_seitzEx hIL.1) hIL.2.2
      (gls3PlusRankOneCharThree_of_reeG2 y05)
  exact CFSG.AGLEmbeddingD2.lc_gl_embedding_theorem_d2_rank_four_of_frontier_tight
    (CFSG.AGLEmbeddingD2.d1For_of_canonical hD1) hIL.2 hCIT y11 hGLSPlus
    (CFSG.AGLEmbeddingD2.Tits.GN516.agl81I516_of_graphOrbit y06 y07)
    CFSG.AGLEmbeddingD2.McLaughlin.A7Six.gnAltSevenThreeRank_proved hsh.1 hsh.2.1 hFO hCF
    G hnonab hK hchar he hδ₁ hδ₂ p hp P M hM hPM Q hQ hQrank hQM H hH hQH

end CFSG.Yardstones.M19b85589cdfc
