module

public import CFSG.HardMathSupport.Lang.AnisoE6.F4GraphFixed
public import CFSG.RankThree.Classical2.TwistedE6RationalOrder
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLM2
public import CFSG.LieType.Chevalley.E6ToralGraphInvolution
public import Mathlib.FieldTheory.AlgebraicClosure
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignCores
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7Split
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLTorus
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Open.QuasithinDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType.NoOffTwE6Three

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.AnisoE6 CFSG.SeitzReduction.F4Pilot CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem e6FixedF4EquivAll_symm_mem_torusGroup {K : Type} [Field K]
    (g : twistedFixedGroup TwistTag.E6 K (RingHom.id K))
    (hg : (e6FixedF4EquivAll K g : ModGL Tag.F4 K) ∈ torusGroup Tag.F4 K) :
    (g : ModGL TwistTag.E6.tag K) ∈ torusGroup Tag.E6 K := by
  classical
  let Ω := AlgebraicClosure K
  let ι : K →+* Ω := algebraMap K Ω
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  let gΩ : twistedFixedGroup TwistTag.E6 Ω (RingHom.id Ω) :=
    ⟨baseChangeGL ι (g : ModGL TwistTag.E6.tag K),
      baseChangeGL_mem_twistedFixedGroup ι g.2⟩
  have hgF4 : (e6FixedF4EquivAll Ω gΩ : ModGL Tag.F4 Ω) ∈ torusGroup Tag.F4 Ω := by
    rw [coe_e6FixedF4EquivAll]
    rw [show e6FixedToF4 Ω gΩ = baseChangeGL ι (e6FixedToF4 K g) from
      e6FixedToF4_baseChangeGL ι g]
    exact baseChangeGL_mem_torusGroup ι hg
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hgF4
  let a : Fin Tag.E6.rank → Ωˣ := fun i => b (e6IndexToF4 i)
  have ha : ∀ i, a (rhoE6 i) = a i := fun i => by
    simp only [a, e6IndexToF4_rhoE6]
  have hperm : (TwistTag.E6.perm).symm = TwistTag.E6.perm := by
    rw [show TwistTag.E6.perm = LargeEvenRhoE6 from rfl]
    ext j
    fin_cases j <;> decide
  have ha' : ∀ i, a ((TwistTag.E6.perm).symm i) = a i := fun i => by
    rw [show (TwistTag.E6.perm).symm = TwistTag.E6.perm from hperm]
    exact ha i
  have hdaT : rootDiagUnit TwistTag.E6.tag a ∈ torusGroup Tag.E6 Ω :=
    rootDiagUnit_mem_torusGroup a
  have hdaG : rootDiagUnit TwistTag.E6.tag a ∈ adjointGroup Tag.E6 Ω :=
    torusGroup_le_adjointGroup_of_field hdaT
  have hdaP : diagramMap TwistTag.E6 Ω * rootDiagUnit TwistTag.E6.tag a =
      rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 Ω := by
    rw [diagramMap_mul_rootDiagUnit (t := TwistTag.E6) a]
    congr 1
  have hdaΓ : rootDiagUnit TwistTag.E6.tag a ∈
      twistedFixedGroup TwistTag.E6 Ω (RingHom.id Ω) :=
    (mem_twistedFixedGroup_id_iff (K := Ω)).2 ⟨hdaG, hdaP⟩
  let dΓ : twistedFixedGroup TwistTag.E6 Ω (RingHom.id Ω) :=
    ⟨rootDiagUnit TwistTag.E6.tag a, hdaΓ⟩
  have hb' : e6FixedToF4 Ω gΩ = rootDiagUnit Tag.F4 b := by
    rw [← coe_e6FixedF4EquivAll]
    exact hb
  have hΨd : e6FixedF4EquivAll Ω dΓ = e6FixedF4EquivAll Ω gΩ := by
    apply Subtype.ext
    rw [coe_e6FixedF4EquivAll, coe_e6FixedF4EquivAll, hb']
    rw [show e6FixedToF4 Ω dΓ = rootDiagUnit Tag.F4 (fun j => a (f4IndexRep j)) from
      e6FixedToF4_rootDiagUnit ha hdaΓ]
    congr 1
    funext j
    simp only [a, e6IndexToF4_f4IndexRep]
  have hgΩ : gΩ = dΓ := (e6FixedF4EquivAll Ω).injective hΨd.symm
  have hbase : baseChangeGL ι (g : ModGL TwistTag.E6.tag K) ∈ torusGroup Tag.E6 Ω := by
    have hval : (gΩ : ModGL TwistTag.E6.tag Ω) = rootDiagUnit TwistTag.E6.tag a := by
      have := congrArg (fun z : twistedFixedGroup TwistTag.E6 Ω (RingHom.id Ω) =>
        (z : ModGL TwistTag.E6.tag Ω)) hgΩ
      simpa [dΓ] using this
    rw [show (gΩ : ModGL TwistTag.E6.tag Ω) =
      baseChangeGL ι (g : ModGL TwistTag.E6.tag K) from rfl] at hval
    rw [hval]
    exact hdaT
  exact mem_torusGroup_of_baseChangeGL_mem ι g.2.1 hbase

end CFSG.StandardType.NoOffTwE6Three
