module

public import Certificates.Certificate3951
public import CFSG.LocalAnalysis.SeitzReduction.EPilotFusionEntrywise
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots
import CFSG.LocalAnalysis.SeitzReduction.E8PilotPositionCenter
import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviAut
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.Open.Defs
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.CharacterTheory.Semidihedral.OddFieldLift
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
import CFSG.LieType.Ree.LargeReeEightTorus
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.SectionRank.BruhatLift
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
import CFSG.LocalAnalysis.SectionRank.LargeReeCover
import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYF3Exact
import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesRoots
import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHighE6
import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7Split
import CFSG.Open.QuasithinDefs
import CFSG.Sporadic.Schreier.TitsOther

public section

namespace CFSG.StandardType.FF81

open CFSG.Blueprint.Chevalley CFSG.SeitzReduction

theorem exists_twoRadical_of_conj_eq_pinnedElt
    {G : Type} [Group G] [Finite G] {Y : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
    (φ : ↥Y ≃* adjointGroup .E6 K) (hK : Nat.card K = 2) {t : G} (htY : t ∈ Y)
    {c : adjointGroup .E6 K}
    (hc : c * φ ⟨t, htY⟩ * c⁻¹ = EPilot.pinnedElt .E6 (highRoot .E6) (1 : K)) :
    ∃ Q : Subgroup G, IsPGroup 2 Q ∧ Q ≤ Y ⊓ Subgroup.centralizer ({t} : Set G) ∧
      (∀ x ∈ Y ⊓ Subgroup.centralizer ({t} : Set G), ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧
      Nat.card ↥(Y ⊓ Subgroup.centralizer ({t} : Set G)) = Nat.card Q * CFSG.Open.ordA 5 2 := by
  set α : Fin (Tag.rank .E6) → ℤ := Pi.single (0 : Fin 6) 1 with hα
  set x₀ : adjointGroup .E6 K := EPilot.pinnedElt .E6 α (1 : K) with hx₀
  set Q₀ : Subgroup (adjointGroup .E6 K) := EPilot.rootRadical .E6 K α with hQ₀
  set M₀ : Subgroup (adjointGroup .E6 K) := EPilot.rootPerpLevi .E6 K α with hM₀
  have hdec : F4Pilot.IsTwoRadicalDecomp x₀ Q₀ M₀ := by
    rw [hx₀, hQ₀, hM₀, hα]
    exact EPilot.isTwoRadicalDecomp_root (Or.inl rfl) (isRoot_single .E6 (0 : Fin 6)) one_ne_zero
  obtain ⟨hQ₀2, hsup, hinf, hnorm⟩ := hdec
  have hdec : F4Pilot.IsTwoRadicalDecomp x₀ Q₀ M₀ := ⟨hQ₀2, hsup, hinf, hnorm⟩
  obtain ⟨m, hm⟩ :=
    E8Pilot.exists_conj_pinnedElt_highRoot_eq (K := K) (Or.inl rfl)
      (isRoot_single .E6 (0 : Fin 6))
  have hm' : m * EPilot.pinnedElt .E6 (highRoot .E6) (1 : K) * m⁻¹ = x₀ := by
    rw [hx₀, hα]
    exact hm
  set d : adjointGroup .E6 K := m * c with hddef
  have hd : d * φ ⟨t, htY⟩ * d⁻¹ = x₀ := by
    rw [hddef]
    calc (m * c) * φ ⟨t, htY⟩ * (m * c)⁻¹
        = m * (c * φ ⟨t, htY⟩ * c⁻¹) * m⁻¹ := by group
      _ = m * EPilot.pinnedElt .E6 (highRoot .E6) (1 : K) * m⁻¹ := by rw [hc]
      _ = x₀ := hm'
  set e : MulAut (adjointGroup .E6 K) := MulAut.conj d⁻¹ with he
  have hex : e x₀ = φ ⟨t, htY⟩ := by
    rw [he]
    change d⁻¹ * x₀ * (d⁻¹)⁻¹ = φ ⟨t, htY⟩
    rw [← hd]
    group
  set Q₁ : Subgroup (adjointGroup .E6 K) := Q₀.map e.toMonoidHom with hQ₁
  set M₁ : Subgroup (adjointGroup .E6 K) := M₀.map e.toMonoidHom with hM₁
  have hdecE : F4Pilot.IsTwoRadicalDecomp (φ ⟨t, htY⟩) Q₁ M₁ := by
    have h := F4Pilot.IsTwoRadicalDecomp.map hdec e
    rw [hex] at h
    simpa only [hQ₁, hM₁] using h
  obtain ⟨hQ₁2, hsup₁, hinf₁, hnorm₁⟩ := hdecE
  set T : Subgroup (adjointGroup .E6 K) :=
    Subgroup.centralizer ({φ ⟨t, htY⟩} : Set (adjointGroup .E6 K)) with hT
  have hsup₁T : Q₁ ⊔ M₁ = T := by
    rw [hT]
    exact hsup₁
  have hTleNorm : T ≤ Subgroup.normalizer (Q₁ : Set (adjointGroup .E6 K)) := by
    rw [← hsup₁T]
    exact sup_le Subgroup.le_normalizer hnorm₁
  set S : Subgroup G := Y ⊓ Subgroup.centralizer ({t} : Set G) with hS
  set f : adjointGroup .E6 K →* G := Y.subtype.comp φ.symm.toMonoidHom with hf
  have hf_inj : Function.Injective f := by
    rw [hf]
    intro x y hxy
    exact φ.symm.injective (Subtype.ext hxy)
  have hQ2 : IsPGroup 2 (Q₁.map f) := hQ₁2.map f
  have hSsub : S.subgroupOf Y = Subgroup.centralizer ({⟨t, htY⟩} : Set ↥Y) := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx
      have hx' : (x : G) ∈ Subgroup.centralizer ({t} : Set G) := hx.2
      rw [Subgroup.mem_centralizer_iff] at hx'
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (hx' t (Set.mem_singleton t)).symm
    · intro hx
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      refine ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst h
      exact (Subtype.ext_iff.mp (Subgroup.mem_centralizer_singleton_iff.mp hx)).symm
  have hSmap : (S.subgroupOf Y).map φ.toMonoidHom = T := by
    rw [hSsub, hT]
    exact CFSG.Walter.map_centralizer_singleton_mulEquiv φ ⟨t, htY⟩
  have hSmap_symm : T.map φ.symm.toMonoidHom = S.subgroupOf Y := by
    rw [← hSmap, Subgroup.map_map]
    rw [show φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id ↥Y from by
      ext x; simp, Subgroup.map_id]
  have hSmap' : T.map f = S := by
    rw [hf, ← Subgroup.map_map, hSmap_symm,
      Subgroup.map_subgroupOf_eq_of_le (inf_le_left : S ≤ Y)]
  have hQleS : Q₁.map f ≤ S := by
    rw [← hSmap']
    exact Subgroup.map_mono (hsup₁T ▸ le_sup_left)
  have hQnorm : ∀ x ∈ S, ∀ q ∈ Q₁.map f, x * q * x⁻¹ ∈ Q₁.map f := by
    intro x hx q hq
    rw [← hSmap'] at hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hq
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨b * a * b⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hTleNorm hb) a).mp ha
    · simp only [map_mul, map_inv]
  have hcardSsub : Nat.card S = Nat.card (S.subgroupOf Y) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : S ≤ Y)).toEquiv]
  have hcardS : Nat.card S = Nat.card T := by
    calc Nat.card S = Nat.card (S.subgroupOf Y) := hcardSsub
      _ = Nat.card ((S.subgroupOf Y).map φ.toMonoidHom) :=
            (Subgroup.card_map_of_injective φ.injective).symm
      _ = Nat.card T := by rw [hSmap]
  have hcardQ₁ : Nat.card Q₁ = Nat.card Q₀ := by
    rw [hQ₁, Subgroup.card_map_of_injective e.injective]
  have hcardM₁ : Nat.card M₁ = Nat.card M₀ := by
    rw [hM₁, Subgroup.card_map_of_injective e.injective]
  have hcardM₀ : Nat.card M₀ = CFSG.Open.ordA 5 2 := by
    rw [hM₀, hα]
    simpa [pow_one] using E6Pilot.card_rootPerpLevi_single_zero (f := 1) (by simpa using hK)
  have hcardT : Nat.card T = Nat.card Q₁ * Nat.card M₁ := by
    rw [← hsup₁T]
    calc Nat.card ↥(Q₁ ⊔ M₁) = Nat.card ↥(Q₀ ⊔ M₀) := by
          rw [hQ₁, hM₁, ← Subgroup.map_sup,
            Subgroup.card_map_of_injective e.injective]
      _ = Nat.card Q₀ * Nat.card M₀ :=
          CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Q₀ M₀ hnorm
            (disjoint_iff.mpr hinf)
      _ = Nat.card Q₁ * Nat.card M₁ := by rw [hcardQ₁, hcardM₁]
  have hcardQ : Nat.card (Q₁.map f) = Nat.card Q₁ :=
    Subgroup.card_map_of_injective hf_inj
  have hcard : Nat.card S = Nat.card (Q₁.map f) * CFSG.Open.ordA 5 2 := by
    calc Nat.card S = Nat.card T := hcardS
      _ = Nat.card Q₁ * Nat.card M₁ := hcardT
      _ = Nat.card (Q₁.map f) * CFSG.Open.ordA 5 2 := by
            rw [← hcardQ, hcardM₁, hcardM₀]
  refine ⟨Q₁.map f, hQ2, hQleS, hQnorm, ?_⟩
  simpa only [hS] using hcard

end CFSG.StandardType.FF81
