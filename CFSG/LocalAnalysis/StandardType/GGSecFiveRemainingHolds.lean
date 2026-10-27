module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeMarkedRank
public import CFSG.LocalAnalysis.StandardType.GGE6R16FieldTwo
public import CFSG.LocalAnalysis.StandardType.GGE6R4FieldTwo
public import CFSG.LocalAnalysis.StandardType.GGE6R3FieldTwo
public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619Triality
public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619G2
public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619E6
public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619ReeProducer
import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619Sp
public import CFSG.LocalAnalysis.StandardType.GGFieldTwoCornerNoSL28Leaves
import CFSG.LocalAnalysis.StandardType.GGKD2SplitLiftHolds
import CFSG.LocalAnalysis.StandardType.GGKD2UnitaryInndiagHolds
import CFSG.LocalAnalysis.StandardType.GGKD2UnitaryBlockHolds
import CFSG.LocalAnalysis.StandardType.GGKD2UnitaryActionHolds
import CFSG.LocalAnalysis.StandardType.GGKD2ConnectedNativeHolds
import CFSG.LocalAnalysis.StandardType.GGKD2A1EightHolds
import CFSG.LocalAnalysis.StandardType.GGKD2SmallA1TwD2Holds
import CFSG.LocalAnalysis.StandardType.GGKD2SmallDerivedSuzukiHolds
import CFSG.LocalAnalysis.StandardType.GGKD2SmallG2DerHolds
import CFSG.LocalAnalysis.StandardType.GGKD2Leaf6Holds
import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619LowAlias
import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619Orth
import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619CoverDescentHolds

public section

namespace CFSG.StandardType

theorem ggE6ThreeI1Rank_holds :
    GGE6ThreeI1Rank := by
  let Omega := AlgebraicClosure (ZMod 2)
  have hQ2R1 : S2MathAs1E6Companion1625.B2SatQ2On Omega GGE6ThreeR1Labels1585 :=
    E6R1FieldTwo.b2SatQ2On_r1_holds Omega
  have hQ2R4 : S2MathAs1E6Companion1625.B2SatQ2On Omega GGE6ThreeR4Labels1585 :=
    E6R4FieldTwo.b2SatQ2On_r4_holds Omega
  have hQ2R16 : S2MathAs1E6Companion1625.B2SatQ2On Omega GGE6ThreeR16Labels1585 :=
    E6R16FieldTwo.b2SatQ2On_r16_holds Omega
  have hInnerR4Opp : ∀ (lab : CFSG.Assembly.LargeEvenLabel) (R : Type) [Group R] (I : Set (MulAut R))
      (phi : MulAut R) (M : GGK0MarkedKacIface1587.MarkedRationalKacRealization Omega lab 3 R I phi)
      (j : Fin M.row.D.orbits.length),
      CFSG.Assembly.LargeEvenInLambda2 lab → (∀ k, k = j) → M.row.D.orbits[j].qs = true →
      GGE6ThreeR4OppLabels1585 lab M.row.D.orbits[j].lab → lab.n = 1 →
      CFSG.HardMathSupport.Timmesfeld.LangTorus.twistInner
        (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom M.a) (M.repr j))
        ((M.setup.ρ : (Fin M.tau.rank → ℤ) → _)^[
          CFSG.HardMathSupport.Timmesfeld.LangTorus.componentOrbitLength M.setup.ρ
            (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom M.a) (M.repr j))]) := by
    intro lab R _ I phi M j hL hj hqs hrow hn
    exact E6R4OppFieldTwo.twistInner_r4Opp M j hL hj hqs hrow hn
  have hQ2R16Opp : S2MathAs1E6Companion1625.B2SatQ2On Omega GGE6ThreeR16OppLabels1585 :=
    E6R16OppFieldTwo.b2SatQ2On_r16Opp_holds Omega
  have hOuterR3Q2 : S2MathAs1E6Companion1625.B3On Omega
      (fun lab labJ => GGE6ThreeR3Labels1585 lab labJ ∧ lab.n = 1) :=
    E6R3FieldTwo.b3On_r3_holds Omega
  have hOuterR16Q2 : S2MathAs1E6Companion1625.B3On Omega
      (fun lab labJ => GGE6ThreeR16Labels1585 lab labJ ∧ lab.n = 1) :=
    E6R16FieldTwo.b3On_r16_q2_holds Omega
  exact E6MarkedRank.i1Rank_of_producers_and_cuts Omega
    GGK0MarkedKacIface1587.e6Producer_holds
    GGK0MarkedKacIface1587.twE6Producer_holds
    hQ2R1 hQ2R4 hQ2R16 hInnerR4Opp hQ2R16Opp
    hOuterR3Q2 hOuterR16Q2

theorem ggFieldTwoCornerNoSL28_holds
    : GGFieldTwoCornerNoSL28 := by
  have hNon : S2MathAs3_1615.corner1584_nonsplit_shape :=
    KD2Pieces1615.corner1584_nonsplit_shape_holds
  have hSplit : S2MathAs3_1615.corner1584_split_lift :=
    KD2Pieces1615.corner1584_split_lift_of_pieces
      (KD2Pieces1615.splitLiftUnitaryThreeDvd_of_pieces KD2Pieces1615.unitaryInndiagIsConj_holds
        KD2Pieces1615.unitaryBlockOfComponent_holds KD2Pieces1615.unitaryBlockAction_holds)
      KD2Pieces1615.splitLiftUnitaryNotThreeDvd_holds
  have hRem : GGCornerRemainingTypes := by
    intro lab hlab
    have hNoSetup : S2MathAs3_1615.RemainingLab lab →
        LargeEvenLabelAll lab (fun R _ I _ => S2MathAs3_1619Final.NoSetupAt R I) := by
      intro hrem
      cases htag : lab.tag with
      | triD4 => exact S2MathAs3_1619Final.noSetupTriD4_holds lab htag hlab
      | D | twD =>
        by_cases hr : 4 ≤ lab.rank
        · have horth : lab.tag = .D ∨ lab.tag = .twD := by simp [htag]
          exact LargeEvenLabelAll.mono
            (fun R _ I _ h => S2MathAs3_1619Final.coverDescent_holds R I h)
            (S2MathAs3_1619Final.actionTag_orth_high
              lab horth hr hlab)
        · by_cases hD : lab.tag = .D
          · have hRank : lab.rank = 3 := by
              have hRank3 : 3 ≤ lab.rank := by simpa [CFSG.Assembly.LargeEvenInLambda2, hD] using hlab.2
              omega
            have hA : CFSG.Assembly.LargeEvenInLambda2 (⟨.A, 3, lab.n⟩ : CFSG.Assembly.LargeEvenLabel) := by
              simp only [CFSG.Assembly.LargeEvenInLambda2]
              exact ⟨hlab.1, by norm_num, by norm_num⟩
            have hNo := S2MathAs3_1619Final.noSetupTag_A_holds
              (⟨.A, 3, lab.n⟩ : CFSG.Assembly.LargeEvenLabel) rfl hA
            intro Q hQ
            have hQA : CFSG.StandardType.LargeEvenRawDatum (⟨.A, 3, lab.n⟩ : CFSG.Assembly.LargeEvenLabel) Q := by
              simpa only [CFSG.StandardType.LargeEvenRawDatum, hD, hRank, ↓reduceIte] using hQ
            simpa only [CFSG.StandardType.LargeEvenRawDatum, hD, hRank, ↓reduceIte] using hNo Q hQA
          · have hTwD : lab.tag = .twD := by simp_all
            have hRank : lab.rank = 3 := by
              have hRank2 : 2 ≤ lab.rank := by
                simpa [CFSG.Assembly.LargeEvenInLambda2, hTwD] using hlab.2
              have hNot2 : lab.rank ≠ 2 := by
                intro heq
                exact hrem.1 (Or.inr (Or.inl ⟨hTwD, heq⟩))
              omega
            exact S2MathAs3_1619Final.noSetupTwD3_of_leaves
              hSplit hNon lab hTwD hRank hlab
      | B =>
        exact LargeEvenLabelAll.mono
          (fun R _ I _ h => S2MathAs3_1619Final.coverDescent_holds R I h)
          (S2MathAs3_1619Final.actionTag_B_holds
            lab htag hlab)
      | C =>
        exact LargeEvenLabelAll.mono
          (fun R _ I _ h => S2MathAs3_1619Final.coverDescent_holds R I h)
          (S2MathAs3_1619Final.actionTag_C_holds
            lab htag hlab)
      | G2 => exact S2MathAs3_1619Final.noSetupG2_holds lab htag hlab
      | F4 | E7 | E8 =>
        have htags : lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8 := by simp [htag]
        exact S2MathAs3_1619Final.noSetupAt_F4E7E8_labelAll hlab htags
      | twF4 =>
        exact S2MathAs3_1619Final.noSetupAt_twF4_labelAll hlab htag
      | A | twA | B2der | G2der | twF4der | twB2 | E6 | twE6 =>
        simp [S2MathAs3_1615.RemainingLab, S2MathAs3_1615.SmallLab,
          S2MathAs3_1615.ClassicalLab, S2MathAs3_1615.E6Lab, htag] at hrem
    by_cases hrem : S2MathAs3_1615.RemainingLab lab
    · refine LargeEvenLabelAll.mono (fun R _ I _ h => ?_) (hNoSetup hrem)
      intro L' _ _ ψ hsurj hker hcomm e J a hsetup _
      exact h L' ψ hsurj hker hcomm e J a hsetup
    · intro Q hQ
      exact largeEvenRawDatum_mono
        (fun R _ I F h => ⟨h, fun L' _ _ ψ _ _ _ e J a _ hr => hrem hr⟩) hQ
  have hE6 : GGCornerE6 := by
    intro lab hlab
    by_cases htag : S2MathAs3_1615.E6Lab lab
    · have he : lab.tag = .E6 ∨ lab.tag = .twE6 := htag
      refine LargeEvenLabelAll.mono (fun R _ I _ h => ?_)
        (S2MathAs3_1619Final.noSetupAt_E6_labelAll hlab he)
      intro L' _ _ ψ hsurj hker hcomm e J a hsetup _
      exact h L' ψ hsurj hker hcomm e J a hsetup
    · intro Q hQ
      exact largeEvenRawDatum_mono
        (fun R _ I F h => ⟨h, fun L' _ _ ψ _ _ _ e J a _ he => (htag he).elim⟩) hQ
  exact ggFieldTwoCornerNoSL28_of_leaves
    (KD2Pieces1615.corner1584_small_labels_of_pieces KD2Pieces1615.smallA1TwD2_holds
      KD2Pieces1615.smallDerivedSuzuki_holds KD2Pieces1615.smallG2Der_holds)
    (KD2Pieces1615.corner1584_connected_of_pieces KD2Pieces1615.connectedNativeAction_holds
      KD2Pieces1615.a1EightInnAutDerived_holds)
    hSplit hRem hE6 hNon

end CFSG.StandardType
