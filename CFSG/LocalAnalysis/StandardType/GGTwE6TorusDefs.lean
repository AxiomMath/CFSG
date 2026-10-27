module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.SeitzGeneration.ExcTorusCatTw
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Four
public import CFSG.LieType.SeitzGeneration.ExcTorusTwE6Three
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A1TwistedE6
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.SigmaPerX
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KGD.D4Frame
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.StandardType.TwE6Tori

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar

@[expose] def twE6Cartan {L : Type} [Field L] :
    (Fin Tag.E6.rank → Lˣ) →* (Fin Tag.E6.rank → Lˣ) where
  toFun := e6RootParams
  map_one' := by
    funext j
    simp [e6RootParams]
  map_mul' u v := by
    funext j
    simp only [e6RootParams, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

@[expose] def twE6Fp {L : Type} [Field L] (Fr : L →+* L) (ω : List (Fin Tag.E6.rank))
    (c : Fin Tag.E6.rank → Lˣ) : Fin Tag.E6.rank → Lˣ :=
  ω.foldr e6StarS (fun i => Units.map Fr.toMonoidHom (c (TwistTag.E6.perm i)))

private theorem twE6StarS_mul {L : Type} [Field L] (j : Fin Tag.E6.rank)
    (t t' : Fin Tag.E6.rank → Lˣ) :
    e6StarS j (t * t') = e6StarS j t * e6StarS j t' := by
  simp only [e6StarS, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, Pi.mulSingle_mul]
  rw [mul_mul_mul_comm]

theorem twE6Fp_mul {L : Type} [Field L] (Fr : L →+* L) (ω : List (Fin Tag.E6.rank))
    (c c' : Fin Tag.E6.rank → Lˣ) :
    twE6Fp Fr ω (c * c') = twE6Fp Fr ω c * twE6Fp Fr ω c' := by
  induction ω with
  | nil =>
    funext i
    simp only [twE6Fp, List.foldr_nil, Pi.mul_apply]
    exact map_mul (Units.map Fr.toMonoidHom) _ _
  | cons j ω ih =>
    simp only [twE6Fp, List.foldr_cons] at ih ⊢
    rw [ih, twE6StarS_mul]

theorem twE6Fp_one {L : Type} [Field L] (Fr : L →+* L) (ω : List (Fin Tag.E6.rank)) :
    twE6Fp Fr ω 1 = 1 := by
  induction ω with
  | nil =>
    funext i
    simp only [twE6Fp, List.foldr_nil, Pi.one_apply]
    exact map_one (Units.map Fr.toMonoidHom)
  | cons j ω ih =>
    simp only [twE6Fp, List.foldr_cons] at ih ⊢
    rw [ih]
    funext i
    simp [e6StarS]

@[expose] def twE6FpHom {L : Type} [Field L] (Fr : L →+* L) (ω : List (Fin Tag.E6.rank)) :
    (Fin Tag.E6.rank → Lˣ) →* (Fin Tag.E6.rank → Lˣ) where
  toFun := twE6Fp Fr ω
  map_one' := twE6Fp_one Fr ω
  map_mul' := twE6Fp_mul Fr ω

@[expose] def twE6Pfix {L : Type} [Field L] (Fr : L →+* L) (ω : List (Fin Tag.E6.rank)) :
    Subgroup (Fin Tag.E6.rank → Lˣ) :=
  (twE6FpHom Fr ω).eqLocus (MonoidHom.id _)

@[expose] noncomputable def twE6Image {L : Type} [Field L] (Fr : L →+* L)
    (ω : List (Fin Tag.E6.rank)) : Subgroup (ModGL Tag.E6 L) :=
  (twE6Pfix Fr ω).map ((rootDiagUnitHom Tag.E6 L).comp twE6Cartan)

end CFSG.StandardType.TwE6Tori

end
