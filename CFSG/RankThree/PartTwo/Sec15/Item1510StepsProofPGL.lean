module

public import CFSG.RankThree.PartTwo.Sec15.Item1510StepsProof
import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec13.Naturality
import CFSG.CharacterTheory.Semidihedral.OddFieldLift
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelSelector
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] noncomputable def Step1510PGLFuse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → All1510 A →
      ∀ B : Subgroup G, IsHyperplane A B → c ∈ B →
        thetaAlpha 3 B ≠ thetaAlpha 3 (A ⊓ L) →
        ∀ P : Subgroup G,
          CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.centralizer (B : Set G)) →
          A ≤ P → A ≠ omegaOneThree P →
          (∃ y ∈ P, ∀ s ∈ A ⊓ L,
            s⁻¹ * y ∉ Late.sectionCentralizer P L (inSubgroup (aschbacherSolvableCore 3) L)) →
          ∀ x ∈ Subgroup.normalizer (B : Set G) ⊓ Subgroup.normalizer (P : Set G),
            (Subgroup.zpowers c).map (MulAut.conj x).toMonoidHom ≠ Subgroup.zpowers c →
              (Subgroup.zpowers c).map (MulAut.conj x).toMonoidHom ∈ omegaA A

namespace Proof1510Steps

variable {G : Type} [Group G] [Finite G]

theorem eq_omegaOneThree_of_inner {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) {B P : Subgroup G} (hcB : c ∈ B)
    (hP : IsPGroup 3 P) (hPB : P ≤ Subgroup.centralizer (B : Set G)) (hAP : A ≤ P)
    (hinner : ∀ y ∈ P, ∃ s ∈ A ⊓ L,
      s⁻¹ * y ∈ Late.sectionCentralizer P L (inSubgroup (aschbacherSolvableCore 3) L)) :
    A = omegaOneThree P := by
  have hD := h.toSec13Data
  have hA := hD.isElemAbelian
  have hcL : c ∉ L := h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  have hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L) :=
    eq_sup_of_card_nine hD h9 fun hc => hcL hc.2
  have hPθ : P ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥ :=
    inf_eq_bot_of_coprime hP (not_three_dvd_card_theta L)
  apply le_antisymm
  · intro a ha
    exact Subgroup.subset_closure ⟨hAP ha, hA.2 a ha⟩
  · rw [omegaOneThree, Subgroup.closure_le]
    rintro z ⟨hzP, hz3⟩
    obtain ⟨s, hs, hk⟩ := hinner z hzP
    have hzsk : z = s * (s⁻¹ * z) := by group
    set k := s⁻¹ * z with hkdef
    have hkS : ∀ s' ∈ A ⊓ L, k * s' = s' * k := by
      intro s' hs'
      have h1 : k * s' * k⁻¹ * s'⁻¹ ∈ P ⊓ inSubgroup (aschbacherSolvableCore 3) L :=
        ⟨P.mul_mem (P.mul_mem (P.mul_mem hk.1 (hAP hs'.1)) (P.inv_mem hk.1))
          (P.inv_mem (hAP hs'.1)), hk.2 s' hs'.2⟩
      rw [hPθ, Subgroup.mem_bot] at h1
      calc k * s' = (k * s' * k⁻¹ * s'⁻¹) * (s' * k) := by group
        _ = s' * k := by rw [h1, one_mul]
    have hAk : A ≤ Subgroup.centralizer ({k} : Set G) := by
      rw [hAeq]
      refine sup_le (Subgroup.zpowers_le.mpr ?_) fun s' hs' => ?_
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp (hPB hk.1) c hcB
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hkS s' hs').symm
    have hk3 : k ^ 3 = 1 := by
      have hcomm : Commute s k := (hkS s hs).symm
      rw [hzsk, hcomm.mul_pow, hA.2 s hs.1, one_mul] at hz3
      exact hz3
    have hkA : k ∈ A := mem_of_mem_partTwoF h.mem_partTwoF hk3 hAk
    rw [SetLike.mem_coe, hzsk]
    exact A.mul_mem hs.1 hkA

theorem mem_normalizer_of_map_mem_omegaA (hset : Item13SetupAt) {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L) (hall : All1510 A) {B : Subgroup G} (hB : IsHyperplane A B)
    {P : Subgroup G} (hP : IsPGroup 3 P)
    (hPB : P ≤ Subgroup.centralizer (B : Set G)) (hAP : A ≤ P) {x : G}
    (hxP : x ∈ Subgroup.normalizer (P : Set G))
    (hF : (Subgroup.zpowers c).map (MulAut.conj x).toMonoidHom ∈ omegaA A) :
    x ∈ Subgroup.normalizer (A : Set G) := by
  have hD := h.toSec13Data
  have hA := hD.isElemAbelian
  obtain ⟨⟨χ⟩, h9⟩ := Proof1510.facts_l34_of_quot hD (hall c L h.mem_lA h.zpowers_mem_omegaA)
  have hcL : c ∉ L := h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  have hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L) :=
    eq_sup_of_card_nine hD h9 fun hc => hcL hc.2
  set S := A ⊓ L with hS
  have hB9 : Nat.card B = 9 := by
    have := hB.2
    rw [hD.card_eq] at this
    omega
  obtain ⟨b, hbB, hbS, hb1⟩ := exists_mem_inf_ne_one hA.1 hD.card_eq hB.1 hB9 inf_le_left h9
  have hPL : P ⊓ L = S := inf_eq_of_isPGroup inf_le_right h9 χ hbS hb1 hP (inf_le_left.trans hAP)
    (hPB.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB)))
  have hcx : (MulAut.conj x).toMonoidHom c = x * c * x⁻¹ := by simp
  have hF' : Subgroup.zpowers (x * c * x⁻¹) ∈ omegaA A := by
    rwa [MonoidHom.map_zpowers, hcx] at hF
  obtain ⟨L', hL'⟩ := hset G h.toPartTwoStanding h.partTwoS_eq A h.mem_partTwoF
    h.not_mem_partTwoT (x * c * x⁻¹) hF'
  have h' : Sec15R G A (x * c * x⁻¹) L' := Proof1511.sec15R_point h hF' hL'
  obtain ⟨-, h9'⟩ := Proof1510.facts_l34_of_quot h'.toSec13Data (hall _ L' hL' hF')
  have hcL' : x * c * x⁻¹ ∉ L' := h.hypS.2.2 _ hF' L' hL'
  have hAeq' : A = Subgroup.zpowers (x * c * x⁻¹) ⊔ (A ⊓ L') :=
    eq_sup_of_card_nine h'.toSec13Data h9' fun hc => hcL' hc.2
  set Lx := L.map (MulAut.conj x).toMonoidHom with hLxdef
  have hLx : Lx ∈ thetaComponentsAt 3 (x * c * x⁻¹) := ((mem_lA_map_conj_iff x).mpr h.mem_lA).1
  have h3 : 3 ∣ Nat.card Lx := by
    rw [hLxdef, Subgroup.card_map_of_injective (MulAut.conj x).injective]
    exact three_dvd_card_of_thetaQuot χ (by rw [KFacts.KS14.card_projSL_three_four]; norm_num)
  have hL'eq : Lx = L' := (h.chosen136.2 _ hF' L' hL').2 Lx hLx h3
  have hPx : P.map (MulAut.conj x).toMonoidHom = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hxP
  have hAL' : A ⊓ L' = S.map (MulAut.conj x).toMonoidHom := by
    have hle : A ⊓ L' ≤ S.map (MulAut.conj x).toMonoidHom := by
      rw [← hPL, Subgroup.map_inf _ _ _ (MulAut.conj x).injective, hPx, ← hLxdef, hL'eq]
      exact inf_le_inf_right L' hAP
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, h9, h9']
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  change A.map (MulAut.conj x).toMonoidHom = A
  conv_lhs => rw [hAeq]
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← hAL', hcx, ← hAeq']

end Proof1510Steps

open Proof1510Steps

theorem step1510PGL_of
    (hset : Item13SetupAt) (hfuse : Step1510PGLFuse) :
    Step1510PGL := by
  intro G _ _ A c L h hall B hB hcB hne P hP hAP hAΩ x hx
  have hD := h.toSec13Data
  obtain ⟨-, h9⟩ := Proof1510.facts_l34_of_quot hD (hall c L h.mem_lA h.zpowers_mem_omegaA)
  have hP3 := hP.isPGroup
  have houter : ∃ y ∈ P, ∀ s ∈ A ⊓ L,
      s⁻¹ * y ∉ Late.sectionCentralizer P L (inSubgroup (aschbacherSolvableCore 3) L) := by
    by_contra hcon
    push Not at hcon
    exact hAΩ (eq_omegaOneThree_of_inner h h9 hcB hP3 hP.le hAP hcon)
  by_cases hcx : (Subgroup.zpowers c).map (MulAut.conj x).toMonoidHom = Subgroup.zpowers c
  · refine mem_normalizer_of_map_mem_omegaA hset h hall hB hP3 hP.le hAP hx.2 ?_
    rw [hcx]
    exact h.zpowers_mem_omegaA
  · exact mem_normalizer_of_map_mem_omegaA hset h hall hB hP3 hP.le hAP hx.2
      (hfuse G A c L h hall B hB hcB hne P hP hAP hAΩ houter x hx hcx)

theorem item1510R_of_fuse
    (h131 : Item131) (h133 : Item133) (hset : Item13SetupAt)
    (hfuse : Step1510PGLFuse) : Item1510R :=
  item1510R_of h131 h133 hset (step1510Plane_of hset) step1510Cent_of (step1510PGL_of hset hfuse)

end CFSG.RankThree.PartTwo.Sec15
