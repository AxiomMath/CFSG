module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGTagsDefs
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCentralizerTUStd
import CFSG.LocalAnalysis.SeitzReduction.F4PilotAutD
import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6
import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviRootSL2
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4Inner
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4InnerVBasic
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2PosCore
import CFSG.LocalAnalysis.StandardType.GGRootCentKGRigid
import CFSG.LocalAnalysis.StandardType.GGRootNormInner
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsBasic
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmBasic
import CFSG.Blueprint.ChevalleyRootGroupsTorus
import CFSG.Blueprint.ChevalleyWeyl
import CFSG.LieType.Chevalley.GraphFixedHighestRoot
import CFSG.LieType.Chevalley.Canonical
import CFSG.LieType.Chevalley.EvenF4ExceptionalRootLayers
import CFSG.LieType.Chevalley.AdjointCenter
import CFSG.LieType.Chevalley.RootCommutatorPairTable
import CFSG.LieType.Ree.Duality
import CFSG.LieType.Ree.LargeReeRootInvolution
import CFSG.ClassicalInvolution.Balance.LayerGenerationShortAdjoint
import CFSG.LieType.Steinberg.Adjoint.Pairs
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
import CFSG.ClassicalInvolution.Balance.PassTwoFinal
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSetup
import CFSG.RankThree.PartOne.AUTSL.OmegaFamily
import CFSG.RankThree.PartOne.AUTSL.Rows
import CFSG.RankThree.PartOne.AUTSL.SylowTrick
import CFSG.RankThree.PartOne.CTP.StrongPSylow
import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
import CFSG.RankThree.PartOne.S12.Sec1511Y1
import CFSG.RankThree.PartOne.S12.Sec15Items
import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootOps CFSG.LieType.Ree CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.SeitzReduction

namespace KGF4

private theorem exists_mulAut_conj_of_mem_normalizer {U G : Type*} [Group U] [Group G]
    {ψ : U →* G} (hψ : Function.Injective ψ) {a : G}
    (ha : a ∈ Subgroup.normalizer (ψ.range : Set G)) :
    ∃ α : MulAut U, ∀ k : U, a * ψ k * a⁻¹ = ψ (α k) := by
  let Θ : U ≃* ψ.range := MonoidHom.ofInjective hψ
  let α : MulAut U := (Θ.trans (ψ.range.normalizerMonoidHom ⟨a, ha⟩)).trans Θ.symm
  have hΘ : ∀ x : U, ((Θ x : ψ.range) : G) = ψ x := fun x => by
    show ((MonoidHom.ofInjective hψ x : ψ.range) : G) = ψ x
    rw [MonoidHom.ofInjective_apply]
  refine ⟨α, fun k => ?_⟩
  have h1 : ((Θ (α k) : ψ.range) : G) = a * ψ k * a⁻¹ := by
    have e : Θ (α k) = ψ.range.normalizerMonoidHom ⟨a, ha⟩ (Θ k) := by
      simp only [α, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rw [e, GGRootNorm.coe_normalizerMonoidHom, hΘ k]
  exact h1.symm.trans (hΘ (α k))

private theorem range_comp_mulAut {U G : Type*} [Group U] [Group G] (ψ : U →* G) (e : MulAut U) :
    (ψ.comp e.toMonoidHom).range = ψ.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, Subgroup.map_top]

section PCore

theorem pCoreOf_le_range_of_zT {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {G : Type} [Group G]
    {ψ : adjointGroup .F4 K →* G} (hψ : Function.Injective ψ)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    pCoreOf 2 (Subgroup.normalizer (ψ.range : Set G) ⊓
      Subgroup.centralizer {ψ (F4Pilot.zT K)}) ≤ ψ.range := by
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  intro a ha
  have haM : a ∈ Subgroup.normalizer (ψ.range : Set G) ⊓
      Subgroup.centralizer {ψ (F4Pilot.zT K)} := GGRootNorm.pCoreOf_le _ ha
  have ha_norm : a ∈ Subgroup.normalizer (ψ.range : Set G) := haM.1
  have haC : a ∈ Subgroup.centralizer ({ψ (F4Pilot.zT K)} : Set G) := haM.2
  obtain ⟨α, hα⟩ := exists_mulAut_conj_of_mem_normalizer hψ ha_norm
  have hαz : α (F4Pilot.zT K) = F4Pilot.zT K := by
    apply hψ
    rw [← hα]
    calc a * ψ (F4Pilot.zT K) * a⁻¹ = ψ (F4Pilot.zT K) * a * a⁻¹ := by
          rw [Subgroup.mem_centralizer_singleton_iff.mp haC]
      _ = ψ (F4Pilot.zT K) := by group
  obtain ⟨-, hnf, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨g, k⟩, hgk, huniq⟩ := hnf α
  set g' : adjointGroup .F4 K := g with hg'def
  have hgk' : α = MulAut.conj g' * (f4Phi (K := K)) ^ (k : ℕ) := hgk
  have hkeven : ∃ j : ℕ, (k : ℕ) = 2 * j := by
    rcases Nat.even_or_odd (k : ℕ) with ⟨j, hj⟩ | ⟨j, hj⟩
    · exact ⟨j, by omega⟩
    · exfalso
      have h1 : g' * ((f4Phi (K := K)) ^ (k : ℕ)) (F4Pilot.zT K) * g'⁻¹ = F4Pilot.zT K := by
        have h := congrArg (fun e : MulAut (adjointGroup .F4 K) => e (F4Pilot.zT K)) hgk'
        simp only [MulAut.mul_apply, MulAut.conj_apply] at h
        exact h.symm.trans hαz
      rw [show F4Pilot.zT K = ⟨f4x K 47 1, pinnedX_mem_adjointGroup _ _⟩ from rfl] at h1
      rw [hj, f4Phi_pow_odd_f4x_47] at h1
      rw [show (⟨f4x K 44 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) =
        F4Pilot.zU K from rfl] at h1
      have h3 : ((g' : ModGL .F4 K) * f4x K 44 1 * ((g' : ModGL .F4 K))⁻¹) = f4x K 47 1 := by
        have := congrArg Subtype.val h1
        simpa [F4Pilot.zT, F4Pilot.zU, f4x] using this
      have h4 : ((g' : ModGL .F4 K))⁻¹ * f4x K 47 1 * (((g' : ModGL .F4 K))⁻¹)⁻¹ =
          f4x K 44 1 := by
        rw [← h3]
        group
      exact conj_f4x_47_ne_f4x_44 (g := ((g' : ModGL .F4 K))⁻¹) (inv_mem g'.2) h4
  obtain ⟨j, hj⟩ := hkeven
  have hpow : ((f4Phi (K := K)) ^ (k : ℕ)) = ((f4Fr (K := K)) ^ j) := by
    rw [hj, f4Phi_pow_two_mul]
  let c : adjointGroup .F4 K →* adjointGroup .F4 K := ((f4Fr (K := K)) ^ j).toMonoidHom
  have hgk'' : α = MulAut.conj g' * ((f4Fr (K := K)) ^ j) := by
    rw [hgk', hpow]
  have hconj : ∀ k' : adjointGroup .F4 K, a * ψ k' * a⁻¹ = ψ (g' * c k' * g'⁻¹) := by
    intro k'
    rw [hα k']
    have h := congrArg (fun e : MulAut (adjointGroup .F4 K) => e k') hgk''
    simp only [MulAut.mul_apply, MulAut.conj_apply] at h
    rw [h]
    rfl
  have hc0 : c (F4Pilot.zT K) = F4Pilot.zT K := by
    refine Subtype.ext ?_
    have h := F4Pilot.coe_f4Fr_pow_f4x (K := K) j 47 1
    rw [one_pow] at h
    simpa [c, F4Pilot.zT] using h
  obtain ⟨hQ2, hCx, hdisj, hLQ⟩ := F4Pilot.isTwoRadicalDecomp_zT (K := K)
  have hQ : pCoreOf 2 (Subgroup.centralizer ({F4Pilot.zT K} : Set (adjointGroup .F4 K))) =
      F4Pilot.radicalT K := by
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
  obtain ⟨h, hhL, hkey⟩ :=
    KGRig.exists_levi_conj_eq_of_mem_pCoreOf hψ hCx.symm hLQ (disjoint_iff.mpr hdisj) hQ ha
      hc0 hconj
  have hγroot : IsRoot .F4 (orbitCertRoot .F4 32) := F4Pilot.long_mem_c3PerpRoots.1
  have hγ4 : iform (orbitCertRoot .F4 32) (orbitCertRoot .F4 32) = 4 :=
    F4Pilot.long_mem_c3PerpRoots.2.1
  have hγmem : orbitCertRoot .F4 32 ∈ F4Pilot.c3LeviRoots :=
    F4Pilot.mem_c3LeviRoots.mpr
      (F4Pilot.mem_c3PerpRoots_iff.mp F4Pilot.long_mem_c3PerpRoots.2.2)
  have hcz : ∀ t : K, c ⟨pinnedX .F4 K (orbitCertRoot .F4 32) t,
      pinnedX_mem_adjointGroup _ _⟩ =
      ⟨pinnedX .F4 K (orbitCertRoot .F4 32) (t ^ ReeTag.F4.prime ^ j),
        pinnedX_mem_adjointGroup _ _⟩ := by
    intro t
    refine Subtype.ext ?_
    exact F4Pilot.coe_f4Fr_pow_pinnedX (K := K) j _ t
  have hfix : ∀ t : K, (MulAut.conj h * (f4Fr (K := K)) ^ j)
      ⟨pinnedX .F4 K (orbitCertRoot .F4 32) t, pinnedX_mem_adjointGroup _ _⟩ =
      ⟨pinnedX .F4 K (orbitCertRoot .F4 32) t, pinnedX_mem_adjointGroup _ _⟩ := by
    intro t
    have hD : (⟨pinnedX .F4 K (orbitCertRoot .F4 32) t,
        pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .F4 K) ∈ F4Pilot.C3Levi K :=
      F4Pilot.pinnedX_mem_C3Levi hγmem t
    have hcD : c ⟨pinnedX .F4 K (orbitCertRoot .F4 32) t, pinnedX_mem_adjointGroup _ _⟩ ∈
        F4Pilot.C3Levi K := by
      rw [hcz t]
      exact F4Pilot.pinnedX_mem_C3Levi hγmem _
    have hk := hkey _ hD hcD
    rw [MulAut.mul_apply, MulAut.conj_apply]
    rw [show ((f4Fr (K := K)) ^ j) ⟨pinnedX .F4 K (orbitCertRoot .F4 32) t,
      pinnedX_mem_adjointGroup _ _⟩ =
      c ⟨pinnedX .F4 K (orbitCertRoot .F4 32) t, pinnedX_mem_adjointGroup _ _⟩ from rfl]
    exact hk
  obtain ⟨g'', hg''⟩ := F4Pilot.exists_eq_conj_of_fix_pinnedX_long hf hK hγroot hγ4
    (MulAut.conj h * (f4Fr (K := K)) ^ j) hfix
  have hFr : ((f4Fr (K := K)) ^ j) = MulAut.conj (h⁻¹ * g'') := by
    have hproof := congrArg (fun e => (MulAut.conj h)⁻¹ * e) hg''
    have h3 : (MulAut.conj h)⁻¹ * (MulAut.conj h * (f4Fr (K := K)) ^ j) =
        (f4Fr (K := K)) ^ j := by group
    rw [h3] at hproof
    have hinv : (MulAut.conj h)⁻¹ = MulAut.conj h⁻¹ :=
      (map_inv (f := MulAut.conj) h).symm
    have hmul : MulAut.conj h⁻¹ * MulAut.conj g'' = MulAut.conj (h⁻¹ * g'') :=
      (map_mul (f := MulAut.conj) h⁻¹ g'').symm
    rw [hinv, hmul] at hproof
    exact hproof
  have hαconj : α = MulAut.conj (g' * h⁻¹ * g'') := by
    rw [hgk'', hFr, ← map_mul, mul_assoc]
  have hpair : α = MulAut.conj (g' * h⁻¹ * g'') *
      (f4Phi (K := K)) ^ ((⟨0, by omega⟩ : Fin (2 * f)) : ℕ) := by
    rw [hαconj]
    simp
  have hk0 : k = ⟨0, by omega⟩ := by
    simpa using (congrArg Prod.snd (huniq (g' * h⁻¹ * g'', ⟨0, by omega⟩) hpair)).symm
  have hαg : α = MulAut.conj g' := by
    rw [hgk', hk0]
    simp
  refine KGRig.mem_range_of_conj_eq hC ha_norm (g := g') fun k' => ?_
  rw [hα k']
  exact congrArg ψ (by rw [hαg, MulAut.conj_apply])

private theorem pCoreOf_le_range_of_zU {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {G : Type} [Group G]
    {ψ : adjointGroup .F4 K →* G} (hψ : Function.Injective ψ)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    pCoreOf 2 (Subgroup.normalizer (ψ.range : Set G) ⊓
      Subgroup.centralizer {ψ (F4Pilot.zU K)}) ≤ ψ.range := by
  have h := pCoreOf_le_range_of_zT (f := f) hf hK
    (ψ := ψ.comp (f4Phi (K := K)).toMonoidHom) (hψ.comp (f4Phi (K := K)).injective) (by
      rw [range_comp_mulAut]
      exact hC)
  have hz : (ψ.comp (f4Phi (K := K)).toMonoidHom) (F4Pilot.zT K) = ψ (F4Pilot.zU K) := by
    change ψ (f4Phi (F4Pilot.zT K)) = ψ (F4Pilot.zU K)
    rw [show f4Phi (F4Pilot.zT K) = F4Pilot.zU K from F4Pilot.graphAutF4_zT]
  rw [range_comp_mulAut, hz] at h
  exact h

end PCore

section RootElt

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem exists_conj_zT_of_pinnedX {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot .F4 γ)
    (h4 : iform γ γ = 4) {c : K} (hc : c ≠ 0) :
    ∃ v : adjointGroup .F4 K, v * F4Pilot.zT K * v⁻¹ =
      ⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup _ _⟩ := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨w, hw⟩ := F4Pilot.exists_smul_eq_of_iform_eq_four hγ h4
  have hr : IsRoot .F4 (orbitCertRoot .F4 47) :=
    (f4_isRoot_pos (i := 47) ⟨by norm_num, by norm_num⟩).1
  set n : adjointGroup .F4 K :=
    ⟨canonicalRep (coxeterSystem .F4) K w,
      canonicalRep_mem_adjointGroup (coxeterSystem .F4) K w⟩ with hn
  set i0 : Fin (Tag.rank .F4) := ⟨0, by decide⟩ with hi0
  set t : Kˣ := Units.mk0 c hc with ht
  set d : adjointGroup .F4 K :=
    ⟨torusElt .F4 K i0 t, torusElt_mem_adjointGroup _ t⟩ with hd
  have hE : (∑ j, Tag.cartan .F4 i0 j * (orbitCertRoot .F4 47) j) = 1 := by
    rw [hi0]
    decide
  have hdconj : d * F4Pilot.zT K * d⁻¹ =
      ⟨pinnedX .F4 K (orbitCertRoot .F4 47) c, pinnedX_mem_adjointGroup _ _⟩ := by
    refine Subtype.ext ?_
    have h := root_torus_conjugation (τ := .F4) (R := K)
      (i := i0) (α := orbitCertRoot .F4 47) hr t 1
    have ht1 : ((t ^ (1 : ℤ) : Kˣ) : K) = c := by
      rw [zpow_one]
      rfl
    rw [hE, mul_one, ht1] at h
    simpa [d, F4Pilot.zT, f4x] using h
  have hnconj : n * ⟨pinnedX .F4 K (orbitCertRoot .F4 47) c, pinnedX_mem_adjointGroup _ _⟩ *
      n⁻¹ = ⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup _ _⟩ := by
    refine Subtype.ext ?_
    have h := CFSG.LieType.Chevalley.canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hr c
    rw [hw] at h
    simpa [n] using h
  refine ⟨n * d, ?_⟩
  rw [show (n * d) * F4Pilot.zT K * (n * d)⁻¹ = n * (d * F4Pilot.zT K * d⁻¹) * n⁻¹
    from by group, hdconj, hnconj]

private theorem exists_conj_zU_of_pinnedX {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot .F4 γ)
    (hshort : iform γ γ = 2) {c : K} (hc : c ≠ 0) :
    ∃ v : adjointGroup .F4 K, v * F4Pilot.zU K * v⁻¹ =
      ⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup _ _⟩ := by
  let γR : Fin ReeTag.F4.tag.rank → ℤ := γ
  have hγR : IsRoot ReeTag.F4.tag γR := hγ
  have hshortR : iform γR γR = 2 := hshort
  have hlen : ReeTag.F4.lengthParam γR = 1 := by
    refine (ReeTag.lengthParam_eq_one_iff (t := ReeTag.F4) (α := γR)).mpr ?_
    rw [ReeTag.quadForm_eq_iform]
    exact hshortR
  have hlenR : ReeTag.F4.lengthParam (ReeTag.F4.dualRoot γR) = ↑ReeTag.F4.prime := by
    have h := ReeTag.lengthParam_dualRoot_mul (t := ReeTag.F4) hγR
    rw [hlen, mul_one] at h
    exact h
  have hαrootR : IsRoot ReeTag.F4.tag (ReeTag.F4.dualRoot γR) :=
    ReeTag.isRoot_dualRoot (t := ReeTag.F4) hγR
  have hαlongR : ReeTag.F4.dualRoot γR ∈ ReeTag.F4.longRoots := ⟨hαrootR, hlenR⟩
  have hα4 : iform (ReeTag.F4.dualRoot γR) (ReeTag.F4.dualRoot γR) = 4 := by
    have h := hlenR
    rw [show ReeTag.F4.prime = 2 from rfl] at h
    change (ReeTag.F4.quadForm (ReeTag.F4.dualRoot γR) : ℚ) / 2 = (2 : ℚ) at h
    have h4 : ((ReeTag.F4.quadForm (ReeTag.F4.dualRoot γR) : ℤ) : ℚ) = 4 := by linarith
    have hq : ReeTag.F4.quadForm (ReeTag.F4.dualRoot γR) = 4 := by exact_mod_cast h4
    rw [← ReeTag.quadForm_eq_iform ReeTag.F4 (ReeTag.F4.dualRoot γR)]
    exact hq
  obtain ⟨v₀, hv₀⟩ := exists_conj_zT_of_pinnedX hαrootR hα4 hc
  refine ⟨f4Phi (K := K) (v₀), ?_⟩
  have h1 : f4Phi (K := K) (v₀) * F4Pilot.zU K * (f4Phi (K := K) (v₀))⁻¹ =
      f4Phi (K := K) (v₀ * F4Pilot.zT K * v₀⁻¹) := by
    rw [map_mul, map_mul, map_inv,
      show f4Phi (K := K) (F4Pilot.zT K) = F4Pilot.zU K from
        CFSG.SeitzReduction.f4Phi_f4x_47_44.1]
  rw [h1, hv₀]
  have h := finiteExceptionalAut_pinnedX_long (K := K) hαlongR c
  rw [ReeTag.dualRoot_dualRoot (t := ReeTag.F4) hγR] at h
  exact h

end RootElt

end KGF4

section Tag

theorem ggRootCentOTwoTag_F4 : GGRootCentOTwoTag .F4 := by
  intro G _ _ n f ψ hadm hrank hker hcomm hmodel hC hB r hr hnsolv
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hadm.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (center_adjointGroup_eq_bot (τ := .F4) (K := GaloisField 2 f)).le
  obtain ⟨hr2, γ, ⟨hγD, -⟩, u, hru⟩ := hr
  change γ ∈ (f4Datum (GaloisField 2 f)).roots at hγD
  have hγ : IsRoot .F4 γ := mem_adjDatum_roots.mp hγD
  rw [ggRootSub] at hru
  obtain ⟨z, hz, hzr⟩ := Subgroup.mem_map.mp hru
  obtain ⟨y₀, hy₀, hyz⟩ := Subgroup.mem_map.mp hz
  change (Fin Tag.F4.rank → ℤ) at γ
  rw [← hyz, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzr
  change y₀ ∈ rootGroup (rootOperatorFamily .F4) (GaloisField 2 f) γ at hy₀
  have hy1 : y₀ ≠ 1 := by
    intro h1
    rw [h1, mul_one, mul_inv_cancel, map_one] at hzr
    rw [← hzr, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  obtain ⟨c, hc_eq⟩ := exists_of_mem_rootGroup (F := rootOperatorFamily .F4) hγ hy₀
  have hc : c ≠ 0 := by
    rintro rfl
    refine hy1 ?_
    rw [hc_eq, ← xPar_of_isRoot (F := rootOperatorFamily .F4) hγ (0 : GaloisField 2 f),
      xPar_zero]
    rfl
  have hy₀pin : y₀ =
      ⟨pinnedX .F4 (GaloisField 2 f) γ
        ((((rootOperatorFamily .F4).pinnedFamilySign γ : ℤ) : GaloisField 2 f) * c),
        pinnedX_mem_adjointGroup _ _⟩ := by
    refine Subtype.ext ?_
    rw [hc_eq, ← xPar_of_isRoot (F := rootOperatorFamily .F4) hγ c,
      CFSG.ClassicalInvolution.Balance.coe_xPar_eq_pinnedX hγ c]
  have hsign : ((((rootOperatorFamily .F4).pinnedFamilySign γ : ℤ) :
      GaloisField 2 f)) ≠ 0 := by
    rcases (rootOperatorFamily .F4).pinnedFamilySign_eq γ with h | h <;> rw [h] <;> norm_num
  have hc' : ((((rootOperatorFamily .F4).pinnedFamilySign γ : ℤ) :
      GaloisField 2 f)) * c ≠ 0 := mul_ne_zero hsign hc
  let u' : adjointGroup .F4 (GaloisField 2 f) := u
  let Ψ : adjointGroup .F4 (GaloisField 2 f) →* G := ψ
  have hΨ : Function.Injective Ψ := hinj
  have hCΨ : Subgroup.centralizer (Ψ.range : Set G) = ⊥ := hC
  rcases iform_self_cases noG2_F4 hγ with h2 | h4
  ·
    obtain ⟨v, hv⟩ := KGF4.exists_conj_zU_of_pinnedX hγ h2 hc'
    have hv' : v * F4Pilot.zU (GaloisField 2 f) * v⁻¹ = y₀ := by
      rw [hv, hy₀pin]
    let v' : adjointGroup .F4 (GaloisField 2 f) := v
    let ψ' : adjointGroup .F4 (GaloisField 2 f) →* G :=
      Ψ.comp (MulAut.conj (u' * v')).toMonoidHom
    have hψ' : Function.Injective ψ' := by
      intro x y hxy
      have h1 : (MulAut.conj (u' * v')) x = (MulAut.conj (u' * v')) y :=
        hΨ (by simpa [ψ', MonoidHom.comp_apply] using hxy)
      exact (MulAut.conj (u' * v')).injective h1
    have hrange : ψ'.range = Ψ.range := KGF4.range_comp_mulAut Ψ _
    have hC' : Subgroup.centralizer (ψ'.range : Set G) = ⊥ := by
      rw [hrange]
      exact hCΨ
    have hz' : ψ' (F4Pilot.zU (GaloisField 2 f)) = r := by
      simp only [ψ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show u' * v' * F4Pilot.zU (GaloisField 2 f) * (u' * v')⁻¹ =
        u' * (v' * F4Pilot.zU (GaloisField 2 f) * v'⁻¹) * u'⁻¹ from by group, hv']
      exact hzr
    have hmain := KGF4.pCoreOf_le_range_of_zU (K := GaloisField 2 f) (f := f) hf hK hψ' hC'
    rw [hrange, hz'] at hmain
    exact hmain
  ·
    obtain ⟨v, hv⟩ := KGF4.exists_conj_zT_of_pinnedX hγ h4 hc'
    have hv' : v * F4Pilot.zT (GaloisField 2 f) * v⁻¹ = y₀ := by
      rw [hv, hy₀pin]
    let v' : adjointGroup .F4 (GaloisField 2 f) := v
    let ψ' : adjointGroup .F4 (GaloisField 2 f) →* G :=
      Ψ.comp (MulAut.conj (u' * v')).toMonoidHom
    have hψ' : Function.Injective ψ' := by
      intro x y hxy
      have h1 : (MulAut.conj (u' * v')) x = (MulAut.conj (u' * v')) y :=
        hΨ (by simpa [ψ', MonoidHom.comp_apply] using hxy)
      exact (MulAut.conj (u' * v')).injective h1
    have hrange : ψ'.range = Ψ.range := KGF4.range_comp_mulAut Ψ _
    have hC' : Subgroup.centralizer (ψ'.range : Set G) = ⊥ := by
      rw [hrange]
      exact hCΨ
    have hz' : ψ' (F4Pilot.zT (GaloisField 2 f)) = r := by
      simp only [ψ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show u' * v' * F4Pilot.zT (GaloisField 2 f) * (u' * v')⁻¹ =
        u' * (v' * F4Pilot.zT (GaloisField 2 f) * v'⁻¹) * u'⁻¹ from by group, hv']
      exact hzr
    have hmain := KGF4.pCoreOf_le_range_of_zT (K := GaloisField 2 f) (f := f) hf hK hψ' hC'
    rw [hrange, hz'] at hmain
    exact hmain

end Tag

end CFSG.StandardType
