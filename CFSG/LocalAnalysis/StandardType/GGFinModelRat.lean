module

public import CFSG.RankThree.PartOne.KE.CTLangData
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtDatum
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
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
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE

abbrev GGL : Type := AlgebraicClosure (ZMod 2)

@[expose] noncomputable def ggFrobT (f : ℕ) : GGL →+* GGL := iterateFrobenius GGL 2 f

theorem ggFrobT_apply (f : ℕ) (c : GGL) : ggFrobT f c = c ^ 2 ^ f :=
  iterateFrobenius_def 2 f c

@[expose] noncomputable def ggRatEmb (f : ℕ) : GaloisField 2 f →+* GGL :=
  (IsAlgClosed.lift (R := ZMod 2) (S := GaloisField 2 f) (M := GGL)).toRingHom

section Datum


theorem ggDatumExists {τ : Tag} {f : ℕ} (hf : 1 ≤ f) (w : WeylGroup τ) :
    ∃ D : LangDatum τ GGL, D.Φ = Units.map (entrywiseHom (ggFrobT f)) ∧ D.q = 2 ^ f ∧
      D.n = canonicalRep (coxeterSystem τ) GGL w := by
  classical
  let K := GaloisField 2 f
  letI : Algebra K GGL := (ggRatEmb f).toAlgebra
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  haveI : CharP K 2 := inferInstance
  haveI : CharP GGL 2 := inferInstance
  haveI : IsScalarTower (ZMod 2) K GGL :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  haveI : IsAlgClosure K GGL :=
    { isAlgClosed := inferInstance
      isAlgebraic := Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := K) }
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator τ K (ℓ := 2) (f := f) hf GGL w
  exact ⟨LangDatum.ofFrobenius (ggFrobT f) (2 ^ f) (ggFrobT_apply f) w hg0C hg0,
    rfl, rfl, rfl⟩

theorem ggDatumExistsTw {f : ℕ} (hf : 1 ≤ f) (w : WeylGroup TwistTag.E6.tag) :
    ∃ D : LangDatum TwistTag.E6.tag GGL,
      D.Φ = twistHom TwistTag.E6 GGL (ggFrobT f) ∧ D.q = 2 ^ f ∧
      D.n = canonicalRep (coxeterSystem TwistTag.E6.tag) GGL w := by
  classical
  let K := GaloisField 2 f
  letI : Algebra K GGL := (ggRatEmb f).toAlgebra
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  haveI : CharP K 2 := inferInstance
  haveI : CharP GGL 2 := inferInstance
  haveI : IsScalarTower (ZMod 2) K GGL :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  haveI : IsAlgClosure K GGL :=
    { isAlgClosed := inferInstance
      isAlgebraic := Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := K) }
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_twisted K (ℓ := 2) (f := f) hf GGL w
  exact ⟨LangDatum.ofTwist TwistTag.E6 (ggFrobT f) (2 ^ f) (ggFrobT_apply f) w hg0C hg0,
    rfl, rfl, rfl⟩

end Datum

end CFSG.StandardType.GGFinModel
