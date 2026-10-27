module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsExcConj
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExc
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCentralizerTUStd
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotToralCentralizer
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint

section Tags

namespace RootCentQL

open RootCentExc CFSG.SeitzReduction

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem xPar_f4HighRoot (F : RootOperatorFamily .F4) :
    GGRootCentQL (xPar F f4HighRoot (1 : K)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have he : xPar F f4HighRoot (1 : K) = F4Pilot.zT K := by
    refine Subtype.ext ((coe_xPar_eq_pinnedX h2 F isRoot_f4HighRoot 1).trans ?_)
    change pinnedX .F4 K f4HighRoot 1 = pinnedX .F4 K (RootOps.orbitCertRoot .F4 47) 1
    rw [F4Pilot.orbitCertRoot_47_44.1]
    rfl
  have hct := centTwoGen_xPar_highRoot h2 F highRootData_F4
  rw [he] at hct ⊢
  obtain ⟨hQ2, hQL, -, hLQ⟩ := F4Pilot.isTwoRadicalDecomp_zT (K := K)
  exact ⟨_, _, hQ2, hQL, hLQ, F4Pilot.isQuasisimple_C3Levi,
    (le_sup_right.trans hQL.le).trans hct⟩

end RootCentQL

theorem ggRootCentDerivedTag_F4 : GGRootCentDerivedTag .F4 := by
  intro G _ _ p n f ψ hp hp2 _ _ hker hC _ r hr
  have hψ := AutSt.ker_eq_center hker hC
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 ⊢
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hr2
  have hγ' : IsRoot .F4 γ := mem_adjDatum_roots.mp hγ
  have hcz : GGRootCentQL z := RootCentQL.of_mem_rootGroup (K := GaloisField 2 f) _
    (RootCentQL.single_F4 _ (RootCentQL.xPar_f4HighRoot _)) hγ' hz hz1
  have hker' : (MonoidHom.id (ggU .F4 n f).K).ker = ψ.ker := by
    rw [MonoidHom.ker_id, hψ]
    exact (center_adjointGroup_eq_bot (τ := .F4) (K := GaloisField 2 f)).symm
  exact ggRootCentDerivedAt_of_model (π := MonoidHom.id _) Function.surjective_id hker' hp hp2
    (hcz.conj u)

end Tags

end CFSG.StandardType
