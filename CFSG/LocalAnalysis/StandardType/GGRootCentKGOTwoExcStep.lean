module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHigh
public import CFSG.Assembly.Defs

import CFSG.LieType.Chevalley.BorelSelfNormalizer
import CFSG.LieType.Chevalley.OppositeBorel
import CFSG.LieType.Chevalley.IntrinsicSimplePairs
import CFSG.LieType.Chevalley.GraphFixedCenterTrivial
import CFSG.Blueprint.ChevalleyPinnedLemmas
import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
import CFSG.LieType.Chevalley.SylowOpposition
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsBasic
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2PosCore
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSetup
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.AUTSL.OmegaFamily
import CFSG.RankThree.PartOne.AUTSL.Rows
import CFSG.RankThree.PartOne.AUTSL.SylowTrick
import CFSG.RankThree.PartOne.CTP.StrongPSylow
import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.RankThree.PartOne.S12.Sec1511Y1
import CFSG.RankThree.PartOne.S12.Sec15Items
import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic

public section

namespace CFSG.StandardType.KGExc

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
  CFSG.SeitzReduction.EPilot CFSG.LieType.Steinberg.Adjoint CFSG.StandardType
  CFSG.SeitzReduction.OmegaPilot

variable {τ : Tag} {K : Type} [Field K]


private theorem conj_mem_posUnipotent_of_key {σ : K ≃+* K} {g : ModGL τ K}
    (hg : g ∈ rootSpan τ K (perpRoots τ))
    (hkey : ∀ γ ∈ perpRoots τ, ∀ c : K,
      g * pinnedX τ K γ (σ c) * g⁻¹ = pinnedX τ K γ c)
    {x : ModGL τ K} (hx : x ∈ posUnipotent τ K) :
    g * x * g⁻¹ ∈ posUnipotent τ K := by
  have hle : posUnipotent τ K ≤
      (posUnipotent τ K).comap (MulAut.conj g).toMonoidHom := by
    rw [posUnipotent, rootSpan]
    refine iSup₂_le fun α hα x hx => ?_
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    by_cases hαp : α ∈ perpRoots τ
    · have h := hkey α hαp (σ.symm c)
      rw [RingEquiv.apply_symm_apply] at h
      rw [h]
      exact pinnedX_mem_rootSpan hα (σ.symm c)
    · have hpos : 0 < α (highNode τ) := by
        have h0 : α (highNode τ) ≠ 0 := fun h => hαp ⟨hα.1, h⟩
        exact lt_of_le_of_ne ((IsRoot.height_pos_iff hα.1).1 hα.2 _) (Ne.symm h0)
      have hmem : pinnedX τ K α c ∈ parabolicRadical τ K (perpNodes τ) :=
        pinnedX_mem_rootSpan (mem_parabolicRadicalRoots_perpNodes.2 ⟨hα.1, hpos⟩) c
      exact parabolicRadical_le_posUnipotent (perpNodes τ)
        ((Subgroup.mem_normalizer_iff.1
          (rootSpan_perpRoots_le_normalizer_parabolicRadical hg) _).1 hmem)
  exact hle hx

private theorem rootPerp_neg (γ : Fin τ.rank → ℤ) : rootPerp τ (-γ) = rootPerp τ γ := by
  ext δ
  simp only [rootPerp, Set.mem_setOf_eq]
  rw [iform_neg_right, neg_eq_zero]

private theorem conj_mem_negUnipotent_of_key (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {σ : K ≃+* K} {g : ModGL τ K}
    (hg : g ∈ rootSpan τ K (perpRoots τ))
    (hkey : ∀ γ ∈ perpRoots τ, ∀ c : K,
      g * pinnedX τ K γ (σ c) * g⁻¹ = pinnedX τ K γ c)
    {x : ModGL τ K} (hx : x ∈ negUnipotent τ K) :
    g * x * g⁻¹ ∈ negUnipotent τ K := by
  have hle : negUnipotent τ K ≤
      (negUnipotent τ K).comap (MulAut.conj g).toMonoidHom := by
    rw [negUnipotent, rootSpan]
    refine iSup₂_le fun α hα x hx => ?_
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    by_cases hαp : α ∈ perpRoots τ
    · have h := hkey α hαp (σ.symm c)
      rw [RingEquiv.apply_symm_apply] at h
      rw [h]
      exact pinnedX_mem_rootSpan hα (σ.symm c)
    · have hlt : α (highNode τ) < 0 := by
        have h0 : α (highNode τ) ≠ 0 := fun h => hαp ⟨hα.1, h⟩
        exact lt_of_le_of_ne ((IsRoot.height_neg_iff hα.1).1 hα.2 _) h0
      have hmem : α ∈ radicalRoots τ (-highRoot τ) := by
        refine ⟨hα.1, ?_⟩
        rw [iform_neg_right, iform_comm, iform_highRoot hτ]
        omega
      have hg' : g ∈ rootSpan τ K (rootPerp τ (-highRoot τ)) := by
        rw [rootPerp_neg, rootPerp_highRoot hτ]; exact hg
      have hN := rootSpan_rootPerp_le_normalizer_radicalRoots (K := K) hτ
        (IsRoot.neg (isRoot_highRoot τ))
      have hconj := (Subgroup.mem_normalizer_iff.1 (hN hg') _).1
        (pinnedX_mem_rootSpan (S := radicalRoots τ (-highRoot τ)) hmem c)
      refine rootSpan_le_negUnipotent (S := radicalRoots τ (-highRoot τ)) (fun β hβ => ?_) hconj
      refine ⟨hβ.1, ?_⟩
      rcases IsRoot.height_pos_or_neg hβ.1 with hp | hn
      · have hb := hβ.2
        rw [iform_neg_right, iform_comm, iform_highRoot hτ] at hb
        have hp' := (IsRoot.height_pos_iff hβ.1).1 hp (highNode τ)
        omega
      · exact hn
  exact hle hx

theorem mem_torusGroup_of_conj_perpRoots (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {σ : K ≃+* K}
    {h : adjointGroup τ K} (hh : h ∈ EPilot.perpLevi τ K)
    (hkey : ∀ γ ∈ EPilot.perpRoots τ, ∀ c : K,
      h * EPilot.pinnedElt τ γ (σ c) * h⁻¹ = EPilot.pinnedElt τ γ c) :
    (h : ModGL τ K) ∈ torusGroup τ K := by
  have hD : (h : ModGL τ K) ∈ rootSpan τ K (perpRoots τ) := hh
  have hkey' : ∀ γ ∈ perpRoots τ, ∀ c : K,
      (h : ModGL τ K) * pinnedX τ K γ (σ c) * (h : ModGL τ K)⁻¹ = pinnedX τ K γ c :=
    fun γ hγ c => congrArg Subtype.val (hkey γ hγ c)
  have hkeyi : ∀ γ ∈ perpRoots τ, ∀ c : K,
      (h : ModGL τ K)⁻¹ * pinnedX τ K γ (σ.symm c) * ((h : ModGL τ K)⁻¹)⁻¹ =
        pinnedX τ K γ c := by
    intro γ hγ c
    have h0 := hkey' γ hγ (σ.symm c)
    rw [RingEquiv.apply_symm_apply] at h0
    have h1 : (h : ModGL τ K)⁻¹ * pinnedX τ K γ (σ.symm c) * (h : ModGL τ K) =
        pinnedX τ K γ c := by
      rw [← h0]
      group
    simpa using h1
  have hNpos : (h : ModGL τ K) ∈
      Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact conj_mem_posUnipotent_of_key hD hkey'
    · intro hx
      have hx' := conj_mem_posUnipotent_of_key (σ := σ.symm) (g := (h : ModGL τ K)⁻¹)
        ((rootSpan τ K (perpRoots τ)).inv_mem hD) hkeyi hx
      have e : (h : ModGL τ K)⁻¹ * ((h : ModGL τ K) * x * (h : ModGL τ K)⁻¹) *
          ((h : ModGL τ K)⁻¹)⁻¹ = x := by group
      rwa [e] at hx'
  have hNneg : (h : ModGL τ K) ∈
      Subgroup.normalizer (negUnipotent τ K : Set (ModGL τ K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact conj_mem_negUnipotent_of_key hτ hD hkey'
    · intro hx
      have hx' := conj_mem_negUnipotent_of_key hτ (σ := σ.symm) (g := (h : ModGL τ K)⁻¹)
        ((rootSpan τ K (perpRoots τ)).inv_mem hD) hkeyi hx
      have e : (h : ModGL τ K)⁻¹ * ((h : ModGL τ K) * x * (h : ModGL τ K)⁻¹) *
          ((h : ModGL τ K)⁻¹)⁻¹ = x := by group
      rwa [e] at hx'
  have hB : (h : ModGL τ K) ∈ borelGroup τ K := by
    rw [← (borel_self_normalizers τ K).1]
    exact Subgroup.mem_inf.2 ⟨h.2, hNpos⟩
  have hB' : (h : ModGL τ K) ∈ oppositeBorel τ K := by
    rw [← oppositeBorel_normalizer τ K]
    exact Subgroup.mem_inf.2 ⟨h.2, hNneg⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem τ).length
  rw [← (opposite_Borel_intersection τ K w₀ hw₀).2.2.1]
  exact Subgroup.mem_inf.2 ⟨hB, hB'⟩

theorem eq_one_of_conj_perpRoots (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {σ : K ≃+* K}
    {h : adjointGroup τ K} (hh : h ∈ EPilot.perpLevi τ K)
    (hkey : ∀ γ ∈ EPilot.perpRoots τ, ∀ c : K,
      h * EPilot.pinnedElt τ γ (σ c) * h⁻¹ = EPilot.pinnedElt τ γ c) : σ = 1 := by
  have hT : (h : ModGL τ K) ∈ torusGroup τ K :=
    mem_torusGroup_of_conj_perpRoots hτ hh hkey
  obtain ⟨l, hl⟩ := exists_torus_characters hT
  have hmain : ∀ γ ∈ perpRoots τ, ∀ c : K,
      ((∏ j, l j ^ γ j : Kˣ) : K) * σ c = c := by
    intro γ hγ c
    have h1 : (h : ModGL τ K) * pinnedX τ K γ (σ c) * (h : ModGL τ K)⁻¹ = pinnedX τ K γ c :=
      congrArg Subtype.val (hkey γ hγ c)
    rw [(hl γ hγ.1).2 (σ c)] at h1
    exact pinnedX_injective τ K γ h1
  obtain ⟨j, hj⟩ : ∃ j : Fin τ.rank, j ≠ highNode τ := by
    rcases hτ with rfl | rfl | rfl <;> decide
  have hprod : ((∏ k, l k ^ (Pi.single j 1 : Fin τ.rank → ℤ) k : Kˣ) : K) = (l j : K) := by
    rw [Finset.prod_eq_single j (fun k _ hkj => by rw [Pi.single_eq_of_ne hkj, zpow_zero])
      (by simp), Pi.single_eq_same, zpow_one]
  have h1 := hmain (Pi.single j 1) (single_mem_perpRoots hj) 1
  rw [hprod, map_one, mul_one] at h1
  have hlj : l j = 1 := Units.ext h1
  ext c
  have h2 := hmain (Pi.single j 1) (single_mem_perpRoots hj) c
  rw [hprod, hlj] at h2
  simpa using h2

theorem eq_one_of_perpLevi_conj (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {σ : K ≃+* K}
    {h : adjointGroup τ K} (hh : h ∈ EPilot.perpLevi τ K)
    (hkey : ∀ k ∈ EPilot.perpLevi τ K,
      entrywiseAdjointAut τ σ k ∈ EPilot.perpLevi τ K →
      h * entrywiseAdjointAut τ σ k * h⁻¹ = k) : σ = 1 := by
  refine eq_one_of_conj_perpRoots hτ hh fun γ hγ c => ?_
  have h := hkey (EPilot.pinnedElt τ γ c) (pinnedElt_mem_perpLevi hγ c) ?_
  · rwa [entrywiseAdjointAut_pinnedElt] at h
  · rw [entrywiseAdjointAut_pinnedElt]
    exact pinnedElt_mem_perpLevi hγ (σ c)

theorem centralizer_decomp_highRoot [Finite K] [CharP K 2]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hq : CFSG.IsQuasisimple (EPilot.perpLevi τ K))
    (hZ : Subgroup.center (EPilot.perpLevi τ K) = ⊥) :
    Subgroup.centralizer {EPilot.pinnedElt τ (highRoot τ) (1 : K)} =
        EPilot.highRadical τ K ⊔ EPilot.perpLevi τ K ∧
      EPilot.perpLevi τ K ≤
        Subgroup.normalizer (EPilot.highRadical τ K : Set (adjointGroup τ K)) ∧
      Disjoint (EPilot.highRadical τ K) (EPilot.perpLevi τ K) ∧
      pCoreOf 2 (Subgroup.centralizer {EPilot.pinnedElt τ (highRoot τ) (1 : K)}) =
        EPilot.highRadical τ K := by
  obtain ⟨hQ2, hsup, hinf, hnorm⟩ := isTwoRadicalDecomp_highRoot hτ (c := (1 : K)) one_ne_zero
  haveI : Finite (ModGL τ K) := finite_modGL
  refine ⟨hsup.symm, hnorm, disjoint_iff.2 hinf, ?_⟩
  refine ggRCST_pCoreOf_eq hsup.symm hQ2 hnorm ?_
  intro N hNM hN2 hNN
  have hNn : (N.subgroupOf (EPilot.perpLevi τ K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).2 hNN
  have hN2' : IsPGroup 2 (N.subgroupOf (EPilot.perpLevi τ K)) :=
    hN2.comap_of_injective (EPilot.perpLevi τ K).subtype
      (EPilot.perpLevi τ K).subtype_injective
  have hbot := normal_isPGroup_eq_bot_of_isQuasisimple hq hZ
    (N.subgroupOf (EPilot.perpLevi τ K)) hNn hN2'
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hxM : x ∈ EPilot.perpLevi τ K := hNM hx
  have hxm : (⟨x, hxM⟩ : ↥(EPilot.perpLevi τ K)) ∈
      N.subgroupOf (EPilot.perpLevi τ K) := hx
  rw [hbot, Subgroup.mem_bot] at hxm
  simpa using congrArg Subtype.val hxm

end CFSG.StandardType.KGExc
