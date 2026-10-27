module

public import CFSG.LocalAnalysis.StandardType.GGK0LQDict
public import CFSG.LocalAnalysis.StandardType.GGK0LQPair
public import CFSG.LocalAnalysis.StandardType.GGK0LQTwist
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAll
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8Five
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerResiduals
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwF4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.EvenTrialityOuterInvolutions
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.RankThree.PartOne.KLCE.Sector
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate1
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate2
public import Certificates.Kernel.SporSch.Th.Plane2320

public section

namespace CFSG.StandardType.GGK0LQ

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
  {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}

theorem lq_K1 (hlab : LargeEvenInLambda2 lab) (A : K0LangMark Omega lab p R I phi)
    (P : K0Positions A) (j : Fin A.row.D.orbits.length) (hj : A.row.D.orbits[j].qs = true) :
    (twistKind A.setup.ρ (rootCharHom A.a) (P.repr j) = .inner →
      A.setup.D.q ^ componentOrbitLength A.setup.ρ (componentRoots (rootCharHom A.a) (P.repr j))
        < 4 → ∃ α ∈ componentRoots (rootCharHom A.a) (P.repr j),
          ∃ δ ∈ componentRoots (rootCharHom A.a) (P.repr j), δ ≠ α ∧ δ ≠ -α) ∧
    (twistKind A.setup.ρ (rootCharHom A.a) (P.repr j) = .suN →
      ¬ (compRank (componentRoots (rootCharHom A.a) (P.repr j)) = 2 ∧
        A.setup.D.q ^ componentOrbitLength A.setup.ρ (componentRoots (rootCharHom A.a) (P.repr j))
          = 2)) := by
  have hnot : ¬ ((k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).1 = .A ∧
      ((lqTw A P j = 1 ∧ (k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).2 = 1) ∨
        (lqTw A P j ≠ 1 ∧ (k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).2 = 2)) ∧
      A.row.D.orbits[j].lab.n = 1) := fun h => by
    have := (lq_qs_false_iff A P j).2 h
    rw [hj] at this
    exact absurd this (by decide)
  have hqpow := lq_qpow A P j
  have hnpos := lq_orbit_n_pos A P j hlab.1
  constructor
  · intro hk hQ
    by_contra hcon
    push Not at hcon
    have hrank : ∀ α ∈ componentRoots (rootCharHom A.a) (P.repr j),
        ∀ δ ∈ componentRoots (rootCharHom A.a) (P.repr j), δ = α ∨ δ = -α := by
      intro α hα δ hδ
      by_cases h : δ = α
      · exact Or.inl h
      · exact Or.inr (hcon α hα δ hδ h)
    have h1 := (lq_rankOne_iff A P j).1 hrank
    have hct := lq_compType_single A P j h1
    have hn1 : A.row.D.orbits[j].lab.n = 1 := by
      rw [hqpow] at hQ
      by_contra hne
      have : 2 ≤ A.row.D.orbits[j].lab.n := by omega
      have h4 : 2 ^ 2 ≤ 2 ^ A.row.D.orbits[j].lab.n := Nat.pow_le_pow_right (by norm_num) this
      omega
    exact hnot ⟨by rw [hct], Or.inl ⟨lq_tw_single A P j h1, by rw [hct]⟩, hn1⟩
  · rintro hk ⟨hrk, hq⟩
    have hlen : (lqNodes A P j).length = 2 := by rw [← lq_compRank A P j]; exact hrk
    obtain ⟨-, hnc⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.suN_rank_ncard hk
    have hpair := lq_pair_ncard A P j hlen
    have hfam : (k0CompType (k0DiagOf A.row.T) (lqNodes A P j)).1 = .A := by
      by_contra hne
      rw [if_neg hne] at hpair
      rw [hrk] at hnc
      omega
    have htw : lqTw A P j ≠ 1 := fun h1 => by
      have := (lq_kind_of_A2 A P j hlen hfam).1 h1
      rw [hk] at this
      exact absurd this (by decide)
    have hn1 : A.row.D.orbits[j].lab.n = 1 := by
      rw [hqpow] at hq
      have h2 : (2 : ℕ) ^ A.row.D.orbits[j].lab.n = 2 ^ 1 := by simpa using hq
      exact Nat.pow_right_injective (le_refl 2) h2
    exact hnot ⟨hfam, Or.inr ⟨htw, by rw [lq_compType_A_rank _ _ hfam, hlen]⟩, hn1⟩

theorem lq_K2 (A : K0LangMark Omega lab p R I phi)
    (P : K0Positions A)
    (j : Fin A.row.D.orbits.length) (hj : A.row.D.orbits[j].qs = false) :
    (twistKind A.setup.ρ (rootCharHom A.a) (P.repr j) = .inner ∧
      A.setup.D.q ^ componentOrbitLength A.setup.ρ (componentRoots (rootCharHom A.a) (P.repr j))
        = 2 ∧ ∀ α ∈ componentRoots (rootCharHom A.a) (P.repr j),
          ∀ δ ∈ componentRoots (rootCharHom A.a) (P.repr j), δ = α ∨ δ = -α) ∨
    (twistKind A.setup.ρ (rootCharHom A.a) (P.repr j) = .suN ∧
      compRank (componentRoots (rootCharHom A.a) (P.repr j)) = 2 ∧
      A.setup.D.q ^ componentOrbitLength A.setup.ρ (componentRoots (rootCharHom A.a) (P.repr j))
        = 2) := by
  obtain ⟨hfam, hcase, hn⟩ := (lq_qs_false_iff A P j).1 hj
  have hq : A.setup.D.q ^ componentOrbitLength A.setup.ρ
      (componentRoots (rootCharHom A.a) (P.repr j)) = 2 := by
    rw [lq_qpow A P j, hn]; norm_num
  rcases hcase with ⟨-, hr1⟩ | ⟨htw, hr2⟩
  · have hlen : (lqNodes A P j).length = 1 := by rw [← lq_compType_A_rank _ _ hfam]; exact hr1
    exact Or.inl ⟨lq_kind_of_rankOne A P j hlen, hq, (lq_rankOne_iff A P j).2 hlen⟩
  · have hlen : (lqNodes A P j).length = 2 := by rw [← lq_compType_A_rank _ _ hfam]; exact hr2
    exact Or.inr ⟨(lq_kind_of_A2 A P j hlen hfam).2 htw,
      by rw [lq_compRank A P j]; exact hlen, hq⟩

end CFSG.StandardType.GGK0LQ

end
