module

public import Certificates.Kernel.Cert690.CensSP0
public import Certificates.Kernel.Cert690.CensSP1
public import Certificates.Kernel.Cert690.CensSP2
public import Certificates.Kernel.Cert690.CensSP3
public import Certificates.Kernel.Cert690.CensSPBase
public import Certificates.Kernel.Cert690.CensSBind
public import Certificates.Kernel.Cert690.GlueP
public import Certificates.Kernel.Cert690.PglGlue
public import CFSG.Certificates.Kernel.Cert690.CensusSGoal
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.GF2Type.Smith1979W3.Cert690.Holds
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S5Three
public import CFSG.LargeExtraspecial.S6Four
public import CFSG.LargeExtraspecial.S6SevenC
public import CFSG.LargeExtraspecial.S8FusE
public import CFSG.LargeExtraspecial.S8Lin
public import CFSG.LargeExtraspecial.S9FourD
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureDatum
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Open.QuasithinDefs
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import Certificates.Kernel.Cert690.BfsNeg
public import Certificates.Kernel.Cert690.SqA8Neg
public import Certificates.Kernel.Cert690.SqPassNeg
public import Certificates.Kernel.Cert690.SqPglNeg
public import Certificates.Kernel.Cert690.SqPglNeg4
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.CensSP

open CFSG.KC.C690 CFSG.KC.C690S CFSG.GF2Type.Smith1979W3.Cert690 CFSG.LargeExtraspecial.O62

#kc_forall_tree ok0All (fun i => checkAt base CensSP0.lo CensSP0.ginv CensSP0.wg CensSP0.cpar
  CensSP0.T CensSP0.orb CensSP0.reps CensSP0.ranks CensSP0.recs CensSP0.cls i = true) 156
  CertificateChecks.KernelC690.CensSP0.ok
#kc_forall_tree ok1All (fun i => checkAt base CensSP1.lo CensSP1.ginv CensSP1.wg CensSP1.cpar
  CensSP1.T CensSP1.orb CensSP1.reps CensSP1.ranks CensSP1.recs CensSP1.cls i = true) 156
  CertificateChecks.KernelC690.CensSP1.ok
#kc_forall_tree ok2All (fun i => checkAt base CensSP2.lo CensSP2.ginv CensSP2.wg CensSP2.cpar
  CensSP2.T CensSP2.orb CensSP2.reps CensSP2.ranks CensSP2.recs CensSP2.cls i = true) 156
  CertificateChecks.KernelC690.CensSP2.ok
#kc_forall_tree ok3All (fun i => checkAt base CensSP3.lo CensSP3.ginv CensSP3.wg CensSP3.cpar
  CensSP3.T CensSP3.orb CensSP3.reps CensSP3.ranks CensSP3.recs CensSP3.cls i = true) 156
  CertificateChecks.KernelC690.CensSP3.ok

theorem nF_eq : base.nF = 624 := by decide +kernel

theorem lo_eq : CensSP0.lo = 0 ∧ CensSP1.lo = 156 ∧ CensSP2.lo = 312 ∧ CensSP3.lo = 468 := by
  decide +kernel

theorem sing_nodup : base.sing.Nodup := by decide +kernel

theorem b_lt : base.b < 64 := by decide +kernel

theorem checkFAll : ∀ g < base.nF, ∃ ginv wg cpar T reps recs cls,
    CheckFFacts base g ginv wg cpar T reps recs cls := by
  intro g hg
  rw [nF_eq] at hg
  obtain ⟨l0, l1, l2, l3⟩ := lo_eq
  by_cases h0 : g < 156
  · exact exists_checkF_of_chunk (n := 156) ok0All (by omega) (by omega)
  by_cases h1 : g < 312
  · exact exists_checkF_of_chunk (n := 156) ok1All (by omega) (by omega)
  by_cases h2 : g < 468
  · exact exists_checkF_of_chunk (n := 156) ok2All (by omega) (by omega)
  · exact exists_checkF_of_chunk (n := 156) ok3All (by omega) (by omega)

theorem kPGL_codes : ∀ m ∈ kPGLGens, ∃ Y : V₀ ≃ₗ[ZMod 2] V₀,
    Code.HasCode (Y : V₀ →ₗ[ZMod 2] V₀) m := by
  intro m hm
  obtain ⟨_, -, hmul⟩ :=
    (enumCert_pgl_of_pglFactsCheck CertificateChecks.KernelC690.Pgl.pglFactsP).1.gen_inv m hm
  exact exists_equiv_of_mul_eq_one hmul

theorem censusLGoalP :
    ∀ ci < (candidatesOf false (ldata false ()).Llist).size, CensusLGoal false ci := by
  have hR := GrpP.checks.rel
  rw [GrpP.lenO] at hR
  exact censusLGoal_of_facts GrpP.censusBaseP hR (baseS_sound baseOK) CensSBind.bindP candsEq bEq
    sing_nodup b_lt (fun _ => kPGL_codes) checkFAll

end CertificateChecks.KernelC690.CensSP

end
