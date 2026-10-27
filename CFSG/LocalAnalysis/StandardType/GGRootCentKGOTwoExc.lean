module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGTagsDefs
public import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHigh
public import CFSG.LocalAnalysis.SeitzReduction.EPilotFusionEntrywise
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoExcAut
import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoExcStep
import CFSG.LocalAnalysis.StandardType.GGRootCentKGRigid
import CFSG.LocalAnalysis.StandardType.GGRootNormInner
import CFSG.LocalAnalysis.StandardType.GGStructSOnePrimeRootExc
import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourLevi
import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi
import CFSG.LieType.Chevalley.OddF4CosetDescent
import CFSG.LieType.Steinberg.Isogeny.E7
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction RootCentExc CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule

namespace KGExc

@[expose] def OTwoFaithful {U : Type} [Group U] (z : U) : Prop :=
  ∀ (G : Type) [Group G] (ψ : U →* G), Function.Injective ψ →
    Subgroup.centralizer (ψ.range : Set G) = ⊥ →
    pCoreOf 2 (Subgroup.normalizer (ψ.range : Set G) ⊓ Subgroup.centralizer {ψ z}) ≤ ψ.range

theorem OTwoFaithful.of_mulEquiv {U V : Type} [Group U] [Group V] {z : U} (e : U ≃* V)
    (h : OTwoFaithful (e z)) : OTwoFaithful z := by
  intro G _ ψ hψ hC
  have hr : (ψ.comp e.symm.toMonoidHom).range = ψ.range := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨e.symm y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨e y, by simp⟩
  have hz : (ψ.comp e.symm.toMonoidHom) (e z) = ψ z := by simp
  have h' := h G (ψ.comp e.symm.toMonoidHom) (hψ.comp e.symm.injective) (by rw [hr]; exact hC)
  rw [hr, hz] at h'
  exact h'

theorem OTwoFaithful.map {U : Type} [Group U] {z : U} (h : OTwoFaithful z) (α : MulAut U) :
    OTwoFaithful (α z) :=
  OTwoFaithful.of_mulEquiv (MulEquiv.symm α) (by rwa [MulEquiv.symm_apply_apply])

section HighRoot


variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem pCoreOf_le_range_of_highRoot (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hq : CFSG.IsQuasisimple (EPilot.perpLevi τ K))
    (hZ : Subgroup.center (EPilot.perpLevi τ K) = ⊥) {G : Type} [Group G]
    {ψ : adjointGroup τ K →* G} (hψ : Function.Injective ψ)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    pCoreOf 2 (Subgroup.normalizer (ψ.range : Set G) ⊓
      Subgroup.centralizer {ψ (EPilot.pinnedElt τ (highRoot τ) 1)}) ≤ ψ.range := by
  have hτ' : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := Or.inr hτ
  intro a ha
  have ha_norm : a ∈ Subgroup.normalizer (ψ.range : Set G) := (GGRootNorm.pCoreOf_le _ ha).1
  obtain ⟨g, σ, hconj⟩ := exists_conj_entrywise_of_mem_normalizer hτ hf hK hψ ha_norm
  have hc0 : (entrywiseAdjointAut τ σ).toMonoidHom (EPilot.pinnedElt τ (highRoot τ) (1 : K)) =
      EPilot.pinnedElt τ (highRoot τ) 1 := by
    rw [MulEquiv.coe_toMonoidHom, EPilot.entrywiseAdjointAut_pinnedElt, map_one σ]
  obtain ⟨hCx, hLQ, hdisj, hQ⟩ := centralizer_decomp_highRoot (K := K) hτ' hq hZ
  obtain ⟨h, hh, hkey⟩ := KGRig.exists_levi_conj_eq_of_mem_pCoreOf hψ hCx hLQ hdisj hQ ha hc0
    hconj
  obtain rfl := eq_one_of_perpLevi_conj hτ' hh hkey
  exact KGRig.mem_range_of_conj_eq hC ha_norm (g := g) fun k => by
    rw [hconj, entrywiseAdjointAut_one, MulAut.one_apply]

private theorem oTwoFaithful_xPar_highRoot (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hq : CFSG.IsQuasisimple (EPilot.perpLevi τ K))
    (hZ : Subgroup.center (EPilot.perpLevi τ K) = ⊥) (F : RootOperatorFamily τ)
    {i₀ : Fin τ.rank} (hd : HighRootData τ (highRoot τ) i₀) :
    OTwoFaithful (xPar F (highRoot τ) (1 : K)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have he : xPar F (highRoot τ) (1 : K) = EPilot.pinnedElt τ (highRoot τ) 1 :=
    Subtype.ext (coe_xPar_eq_pinnedX h2 F hd.maxHeight.1 1)
  rw [he]
  intro G _ ψ hψ hC
  exact pCoreOf_le_range_of_highRoot hτ hf hK hq hZ hψ hC

end HighRoot

end KGExc

section Tags

theorem ggRootCentOTwoTag_E8 : GGRootCentOTwoTag .E8 := by
  intro G _ _ n f ψ hadm _ hker _ _ hC _ r hr _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hadm.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, AutSt.ker_eq_center hker hC]
    exact center_adjointGroup_eq_bot (τ := .E8) (K := GaloisField 2 f)
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 ⊢
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hr2
  have hγ' : IsRoot .E8 γ := mem_adjDatum_roots.mp hγ
  have hcz : KGExc.OTwoFaithful z :=
    RootCentQLTyped.of_mem_rootGroup (P := KGExc.OTwoFaithful) (fun α z h => h.map α) _
      (fun j => RootCentQLTyped.single_E8 (P := KGExc.OTwoFaithful) (fun α z h => h.map α) _
        (KGExc.oTwoFaithful_xPar_highRoot (Or.inr rfl) hf hK E8Pilot.isQuasisimple_e7Levi
          E8Pilot.center_e7Levi_eq_bot _ highRootData_E8) j) hγ' hz hz1
  exact hcz.map (MulAut.conj u) G ψ hinj hC

theorem ggRootCentOTwoTag_E7 : GGRootCentOTwoTag .E7 := by
  intro G _ _ n f ψ hadm _ hker _ _ hC _ r hr _
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hadm.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, AutSt.ker_eq_center hker hC]
    exact E8Pilot.center_minGroup_e7_eq_bot
  obtain ⟨hr2, γ, ⟨hγ, -⟩, u, hru⟩ := hr
  change Fin Tag.E7.rank → ℤ at γ
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 ⊢
  set e := E8Pilot.e7MinEquivAdjoint (GaloisField 2 f) with he
  have hz1 : e z ≠ 1 := by
    intro h
    have hz : z = 1 := e.injective (h.trans (map_one e).symm)
    rw [hz] at hr2
    simp at hr2
  have hγ' : IsRoot .E7 γ := e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 _ |>.mp hγ
  have hez : e z ∈ rootGroup (rootOperatorFamily .E7) (GaloisField 2 f) γ := by
    obtain ⟨c, rfl⟩ := (e7Data_valid.mem_rootGroup _).1 hz
    rw [he, E8Pilot.e7MinEquivAdjoint_apply, e7Isogeny_xm]
    exact xPar_mem hγ' _
  have hcz : KGExc.OTwoFaithful (e z) :=
    RootCentQLTyped.of_mem_rootGroup (P := KGExc.OTwoFaithful) (fun α z h => h.map α) _
      (fun j => RootCentQLTyped.single_E7 (P := KGExc.OTwoFaithful) (fun α z h => h.map α) _
        (KGExc.oTwoFaithful_xPar_highRoot (Or.inl rfl) hf hK E7Pilot.isQuasisimple_perpLevi_E7
          E7Pilot.center_perpLevi_E7_eq_bot _ highRootData_E7) j) hγ' hez hz1
  exact ((KGExc.OTwoFaithful.of_mulEquiv e hcz).map (MulAut.conj u)) G ψ hinj hC

end Tags

end CFSG.StandardType
