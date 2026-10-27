module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructDecomp
import CFSG.LocalAnalysis.StandardType.GGRootCentKGPiece
import CFSG.LocalAnalysis.StandardType.GGRootCentKGMarking
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcConj
import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootExc
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsBasic
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmBasic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCentralizerTUStd
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCentralizerTUPerfect
import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2Position
import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2PosCore
import CFSG.LieType.Chevalley.AdjointCenter
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
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
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
  CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.SeitzReduction
open RootCentExc

section Certificates

namespace KGF4

theorem kgPieces_zT {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) : KGExc.KGPieces (CFSG.SeitzReduction.F4Pilot.zT K) := by
  obtain ⟨hQ2, hCx, hdisj, hLQ⟩ := F4Pilot.isTwoRadicalDecomp_zT (K := K)
  have hQ : pCoreOf 2 (Subgroup.centralizer
      ({F4Pilot.zT K} : Set (adjointGroup .F4 K))) = F4Pilot.radicalT K := by
    refine ggRCST_pCoreOf_eq hCx.symm hQ2 hLQ ?_
    intro N hN hN2 hMN
    set N' : Subgroup ↥(F4Pilot.C3Levi K) := N.subgroupOf (F4Pilot.C3Levi K) with hN'def
    have hN' : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hN).mpr hMN
    have hN'2 : IsPGroup 2 N' :=
      hN2.comap_of_injective (F4Pilot.C3Levi K).subtype (F4Pilot.C3Levi K).subtype_injective
    have hbot : N' = ⊥ := by
      haveI := hN'
      exact OmegaPilot.normal_isPGroup_eq_bot_of_isQuasisimple F4Pilot.isQuasisimple_C3Levi
        F4Pilot.center_C3Levi_eq_bot N' hN' hN'2
    exact RCSTOm.eq_bot_of_subgroupOf_eq_bot hN hbot
  have hperf : ⁅Subgroup.centralizer ({F4Pilot.zT K} : Set (adjointGroup .F4 K)),
      Subgroup.centralizer ({F4Pilot.zT K} : Set (adjointGroup .F4 K))⁆ =
      Subgroup.centralizer ({F4Pilot.zT K} : Set (adjointGroup .F4 K)) := by
    rcases Nat.lt_or_ge f 2 with hlt | hge
    · have hf1 : f = 1 := by omega
      subst hf1
      rw [pow_one] at hK
      exact F4Pilot.commutator_centralizer_zT_two hK
    · have hq : 4 ≤ Nat.card K := by
        rw [hK]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hge
      exact F4Pilot.commutator_centralizer_zT hq
  have hL := isQuasisimple_largeEvenMarking_of_equiv_statedSp (K := K) (m := 3) hK
    (by norm_num) (by simp) (F4Pilot.c3LeviEquiv K).symm
  exact KGExc.kgPieces_of_decomp hCx.symm hQ hLQ hdisj hperf hL.1 hL.2

end KGF4

theorem ggRootCentKGStructTag_F4 : GGRootCentKGStructTag .F4 := by
  intro G _ _ p n f ψ _ _ hadm hrank hker hcomm hLie hC _ _ r hr _ E hEN hEC _ hEinn
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hadm.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (center_adjointGroup_eq_bot (τ := .F4) (K := GaloisField 2 f)).le
  have hEψ : E ≤ ψ.range := by
    intro e he
    exact mem_of_mul_mem_centralizer hC
      (ggPsiDiagInnerAt_of_ggInnerTag .F4 (by simp [GGInnerTag]) G n f ψ ψ.range
        ⟨⟨hadm, hrank⟩, ⟨rfl, hker⟩, hcomm, hLie⟩ e (hEN he) (hEinn e he))
  obtain ⟨hr2, γ, ⟨hγD, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 ⊢
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hr2
  have hbase : KGExc.KGPieces
      (xPar (rootOperatorFamily .F4) f4HighRoot (1 : GaloisField 2 f)) := by
    have hx : xPar (rootOperatorFamily .F4) f4HighRoot (1 : GaloisField 2 f) =
        F4Pilot.zT (GaloisField 2 f) := by
      refine Subtype.ext ((coe_xPar_eq_pinnedX (CharTwo.two_eq_zero) _ isRoot_f4HighRoot 1).trans
        ?_)
      change pinnedX .F4 (GaloisField 2 f) f4HighRoot 1 =
        pinnedX .F4 (GaloisField 2 f) (RootOps.orbitCertRoot .F4 47) 1
      rw [F4Pilot.orbitCertRoot_47_44.1]
      rfl
    rw [hx]
    exact KGF4.kgPieces_zT hf hK
  have hcz : KGExc.KGPieces z :=
    RootCentQLTyped.of_mem_rootGroup (P := KGExc.KGPieces) (fun α z h => h.map α) _
      (fun j => RootCentQLTyped.single_F4 (P := KGExc.KGPieces) (fun α z h => h.map α) _
        hbase j) (mem_adjDatum_roots.mp hγD) hz hz1
  have hKP : KGExc.KGPieces (u * z * u⁻¹) := by
    have h := hcz.map (MulAut.conj u)
    simpa [MulAut.conj_apply] using h
  have hE' : E ≤ ψ.range ⊓ Subgroup.centralizer ({ψ (u * z * u⁻¹)} : Set G) :=
    le_inf hEψ hEC
  exact hKP G ψ hinj E hE'

end Certificates

end CFSG.StandardType
