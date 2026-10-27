module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCentralizerTUStd
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterLang
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.OddShapesPart1
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B2Inner
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.Foundations
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotToralCentralizer
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LnToral
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResidual

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.SeitzReduction.F4Pilot


private theorem spB2_ncard_pair (j : Fin Tag.F4.rank) :
    ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ)).ncard = 2 := by
  rw [Set.ncard_pair]
  intro h
  have := congrFun h j
  simp at this

open CFSG.RankThree.PartOne.KF4 CFSG.HardMathSupport.Timmesfeld.CrossChar in
private theorem spB2_ncard_longA2 :
    (parabolicRoots Tag.F4 f4LongSupport).ncard = 6 := by
  have hnone : none ∉ ({some 0, some 1} : Finset (Option (Fin Tag.F4.rank))) := by
    decide +kernel
  have hCJ : ∀ j : Fin Tag.F4.rank,
      some j ∈ ({some 0, some 1} : Finset (Option (Fin Tag.F4.rank))) ↔ j ∈ f4LongSupport := by
    intro j; rw [mem_f4LongSupport]; revert j; decide +kernel
  have hroots : kacF4.rootsOf (↑({some 0, some 1} : Finset (Option (Fin Tag.F4.rank))) :
      Set (Option (Fin Tag.F4.rank))) = parabolicRoots Tag.F4 f4LongSupport :=
    rootsOf_eq_parabolicRoots_narrow kacF4 facts_F4 (J := f4LongSupport) hnone hCJ
  have hθ : kacF4.θ = ![2, 3, 4, 2] := rfl
  calc (parabolicRoots Tag.F4 f4LongSupport).ncard
      = (kacF4.rootsOf (↑({some 0, some 1} : Finset (Option (Fin Tag.F4.rank))) :
          Set (Option (Fin Tag.F4.rank)))).ncard := by rw [hroots]
    _ = kacCount Tag.F4 kacF4.θ ({some 0, some 1} : Finset (Option (Fin Tag.F4.rank))) :=
        ncard_rootsOf kacF4 facts_F4 ⟨none, hnone⟩
    _ = kacCount Tag.F4 ![2, 3, 4, 2]
        ({some 0, some 1} : Finset (Option (Fin Tag.F4.rank))) := by rw [hθ]
    _ = 6 := by decide +kernel

open CFSG.RankThree.PartOne.KF4 CFSG.HardMathSupport.Timmesfeld.CrossChar in
private theorem spB2_ncard_shortA2 :
    (parabolicRoots Tag.F4 f4ShortSupport).ncard = 6 := by
  have hnone : none ∉ ({some 2, some 3} : Finset (Option (Fin Tag.F4.rank))) := by
    decide +kernel
  have hCJ : ∀ j : Fin Tag.F4.rank,
      some j ∈ ({some 2, some 3} : Finset (Option (Fin Tag.F4.rank))) ↔ j ∈ f4ShortSupport := by
    intro j; rw [mem_f4ShortSupport]; revert j; decide +kernel
  have hroots : kacF4.rootsOf (↑({some 2, some 3} : Finset (Option (Fin Tag.F4.rank))) :
      Set (Option (Fin Tag.F4.rank))) = parabolicRoots Tag.F4 f4ShortSupport :=
    rootsOf_eq_parabolicRoots_narrow kacF4 facts_F4 (J := f4ShortSupport) hnone hCJ
  have hθ : kacF4.θ = ![2, 3, 4, 2] := rfl
  calc (parabolicRoots Tag.F4 f4ShortSupport).ncard
      = (kacF4.rootsOf (↑({some 2, some 3} : Finset (Option (Fin Tag.F4.rank))) :
          Set (Option (Fin Tag.F4.rank)))).ncard := by rw [hroots]
    _ = kacCount Tag.F4 kacF4.θ ({some 2, some 3} : Finset (Option (Fin Tag.F4.rank))) :=
        ncard_rootsOf kacF4 facts_F4 ⟨none, hnone⟩
    _ = kacCount Tag.F4 ![2, 3, 4, 2]
        ({some 2, some 3} : Finset (Option (Fin Tag.F4.rank))) := by rw [hθ]
    _ = 6 := by decide +kernel

theorem rckSpB2_componentRoots_eq {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {a : Fin Tag.F4.rank → Lˣ} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hap : rootDiagUnit Tag.F4 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hrank : compRank (componentRoots (rootCharHom a) i) = 2)
    (hcard : (componentRoots (rootCharHom a) i).ncard = 8) :
    ∃ v : WeylGroup Tag.F4,
      componentRoots (rootCharHom a) i = (fun α => v • α) '' b2LeviRoots := by
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have hpL : (p : L) ≠ 0 := by
    intro h0
    have hdvd : 2 ∣ p := (CharP.cast_eq_zero_iff L 2 p).1 h0
    have h2p : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 hdvd
    exact hp2 h2p.symm
  obtain ⟨v, hcases⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.f4_rank_le_two_component_shape_odd
      hp.pos hodd hpL hap i hrank.le
  rcases hcases with ⟨j, hj⟩ | hlong | hshort | hb2
  · exfalso
    rw [hj, ncard_image_smul, spB2_ncard_pair j] at hcard
    omega
  · exfalso
    rw [hlong, ncard_image_smul, spB2_ncard_longA2] at hcard
    omega
  · exfalso
    rw [hshort, ncard_image_smul, spB2_ncard_shortA2] at hcard
    omega
  · exact ⟨v, hb2⟩

theorem rckSpB2_twistInner {L : Type} [Field L] [IsAlgClosed L]
    {p₀ : ℕ} (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {v : WeylGroup Tag.F4}
    (hv : componentRoots (rootCharHom a) i = (fun α => v • α) '' b2LeviRoots) :
    twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]) := by
  obtain ⟨-, hs, -⟩ := outer_componentOrbitLength_spec S hT i
  exact CFSG.StandardType.F4ExplicitPos.B2Inner.b2_isometry_twistInner
    (isRootComponent_componentRoots i) hv (outer_isIsometry_rho S hs)

end CFSG.StandardType.RCKRP

end
