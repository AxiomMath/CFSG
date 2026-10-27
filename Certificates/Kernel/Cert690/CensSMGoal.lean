module

public import Certificates.Kernel.Cert690.CensSM0
public import Certificates.Kernel.Cert690.CensSM1
public import Certificates.Kernel.Cert690.CensSMBase
public import Certificates.Kernel.Cert690.CensSBind
public import Certificates.Kernel.Cert690.GlueM
public import CFSG.Certificates.Kernel.Cert690.CensusSGoal
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GF2Type.Smith1979W3.Cert690.SoundFB4
public import CFSG.GF2Type.Smith1979W3.Cert690.SoundFB5
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
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.CensSM

open CFSG.KC.C690 CFSG.KC.C690S CFSG.GF2Type.Smith1979W3.Cert690

#kc_forall_tree ok0All (fun i => checkAt base CensSM0.lo CensSM0.ginv CensSM0.wg CensSM0.cpar
  CensSM0.T CensSM0.orb CensSM0.reps CensSM0.ranks CensSM0.recs CensSM0.cls i = true) 126
  CertificateChecks.KernelC690.CensSM0.ok
#kc_forall_tree ok1All (fun i => checkAt base CensSM1.lo CensSM1.ginv CensSM1.wg CensSM1.cpar
  CensSM1.T CensSM1.orb CensSM1.reps CensSM1.ranks CensSM1.recs CensSM1.cls i = true) 125
  CertificateChecks.KernelC690.CensSM1.ok

theorem nF_eq : base.nF = 251 := by decide +kernel

theorem lo_eq : CensSM0.lo = 0 ∧ CensSM1.lo = 126 := by decide +kernel

theorem sing_nodup : base.sing.Nodup := by decide +kernel

theorem b_lt : base.b < 64 := by decide +kernel

theorem checkFAll : ∀ g < base.nF, ∃ ginv wg cpar T reps recs cls,
    CheckFFacts base g ginv wg cpar T reps recs cls := by
  intro g hg
  rw [nF_eq] at hg
  obtain ⟨l0, l1⟩ := lo_eq
  by_cases h0 : g < 126
  · exact exists_checkF_of_chunk (n := 126) ok0All (by omega) (by omega)
  · exact exists_checkF_of_chunk (n := 125) ok1All (by omega) (by omega)

theorem censusLGoalM :
    ∀ ci < (candidatesOf true (ldata true ()).Llist).size, CensusLGoal true ci := by
  have hR := GrpM.checks.rel
  rw [GrpM.lenO] at hR
  exact censusLGoal_of_facts GrpM.censusBaseM hR (baseS_sound baseOK) CensSBind.bindM candsEq bEq
    sing_nodup b_lt (fun h => absurd h (by decide)) checkFAll

end CertificateChecks.KernelC690.CensSM

end
