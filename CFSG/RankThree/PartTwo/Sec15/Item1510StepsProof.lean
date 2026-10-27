module

public import CFSG.RankThree.PartTwo.Sec15.Item1510StepsProofTools
import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec14.Std
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec6.Item612Basic
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaSignalizer
import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
import CFSG.LieType.BorelTits.Basic
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
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
import CFSG.RankThree.PartTwo.Sec6.Item612Core
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

namespace Proof1510Steps

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inSubgroup_theta_le (X : Subgroup G) : inSubgroup (aschbacherSolvableCore 3) X ≤ X :=
  Subgroup.map_subtype_le _

theorem exists_mem_inf_ne_one {A B S : Subgroup G} (hA : IsMulCommutative A)
    (h27 : Nat.card A = 27) (hBA : B ≤ A) (hB9 : Nat.card B = 9) (hSA : S ≤ A)
    (hS9 : Nat.card S = 9) : ∃ b ∈ B, b ∈ S ∧ b ≠ 1 := by
  have hAA : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hA
  have hBS : B ≤ Subgroup.normalizer (S : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _
      ((Subgroup.centralizer_le (s := (S : Set G)) hSA) (hAA (hBA hx)))
  have hcard := Sec6.card_sup_mul_card_inf hBS
  have hle : Nat.card (B ⊔ S : Subgroup G) ≤ 27 := h27 ▸ Subgroup.card_le_of_le (sup_le hBA hSA)
  have hne : B ⊓ S ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot, hB9, hS9] at hcard
    omega
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  exact ⟨b, hb.1, hb.2, fun h => hb1 (Subtype.ext h)⟩


theorem commutator_theta_le_of_point {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (hq : letI := kerAO2_normal h.toSec13Data.le_normalizer
      Nonempty (↥(A ⊔ L) ⧸ kerAO2 A L ≃*
        Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2)))
    {E : Subgroup G} (hEA : E ≤ A) (hcE : c ∈ E) :
    ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (E : Set G)), A⁆ ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) := by
  have hD := h.toSec13Data
  obtain ⟨⟨χ⟩, h9⟩ := Proof1510.facts_l34_of_quot hD hq
  have h3 : 3 ∣ Nat.card L := three_dvd_card_of_thetaQuot χ
    (by rw [KFacts.KS14.card_projSL_three_four]; norm_num)
  have hLN : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    centralizer_le_normalizer_of_three_dvd h.toSec14Std h3
  have hcL : c ∉ L := h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  have hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L) :=
    eq_sup_of_card_nine hD h9 fun hc => hcL hc.2
  set S := A ⊓ L with hS
  set Y := inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (E : Set G)) with hY
  have hYc : Y ≤ Subgroup.centralizer ({c} : Set G) :=
    (inSubgroup_theta_le _).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcE))
  have hAE : A ≤ Subgroup.centralizer (E : Set G) :=
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr hD.isElemAbelian.1).trans
      (Subgroup.centralizer_le hEA)
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    hAE.trans (Subgroup.le_normalizer.trans (Sec6.normalizer_le_normalizer_theta _))
  have hSYL : ⁅S, Y⁆ ≤ Y ⊓ L := by
    rw [Subgroup.commutator_le]
    intro s hs y hy
    rw [commutatorElement_def]
    refine ⟨Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAY hs.1) y).mp hy) (Y.inv_mem hy), ?_⟩
    have h1 : y * s⁻¹ * y⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hLN (hYc hy)) s⁻¹).mp (L.inv_mem hs.2)
    have h2 : s * y * s⁻¹ * y⁻¹ = s * (y * s⁻¹ * y⁻¹) := by group
    rw [h2]
    exact L.mul_mem hs.2 h1
  have hYL : Y ⊓ L ≤ inSubgroup (aschbacherSolvableCore 3) L := by
    refine le_theta_of_le_normalizer inf_le_right h9 χ inf_le_right ?_ ?_
    · exact fun h3' => not_three_dvd_card_theta _
        (h3'.trans (Subgroup.card_dvd_of_le inf_le_left))
    · exact fun s hs =>
        Subgroup.inf_normalizer_le_normalizer_inf ⟨hAY hs.1, Subgroup.le_normalizer hs.2⟩
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
  have hθ : inSubgroup (aschbacherSolvableCore 3) L ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) :=
    Sec6.le_theta_of_normal ((inSubgroup_theta_le L).trans hLc)
      (hLN.trans (Sec6.normalizer_le_normalizer_theta L)) (isSolvable_theta L)
      (not_three_dvd_card_theta L)
  have hcS : Subgroup.zpowers c ≤ Subgroup.normalizer (S : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hD.mem_A, hD.le_normalizer hD.mem_A⟩)
  have hcY : Subgroup.zpowers c ≤ Subgroup.centralizer (Y : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hYc hy)
  have hYA : ⁅Y, A⁆ = ⁅S, Y⁆ := by
    rw [Subgroup.commutator_comm]
    have : ⁅A, Y⁆ = ⁅S ⊔ Subgroup.zpowers c, Y⁆ := by
      rw [sup_comm, ← hAeq]
    rw [this, CFSG.RankThreeEvenClassification.Helpers.normalized_sup_commutator_eq_of_fixed S
      (Subgroup.zpowers c) Y hcS hcY]
  rw [hYA]
  exact hSYL.trans (hYL.trans hθ)

theorem centralizer_le_sup_of_point {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (hq : letI := kerAO2_normal h.toSec13Data.le_normalizer
      Nonempty (↥(A ⊔ L) ⧸ kerAO2 A L ≃*
        Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2)))
    {B : Subgroup G} (hB : IsHyperplane A B) (hcB : c ∈ B) :
    Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (A : Set G) ⊔
      ⁅CFSG.Open.pCoreOf 2 L ⊓ Subgroup.centralizer (B : Set G), A⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD := h.toSec13Data
  have hA := hD.isElemAbelian
  obtain ⟨⟨χ⟩, h9⟩ := Proof1510.facts_l34_of_quot hD hq
  have hθQ := theta_eq_pCoreOf_of_quot hD hq
  have h3 : 3 ∣ Nat.card L := three_dvd_card_of_thetaQuot χ
    (by rw [KFacts.KS14.card_projSL_three_four]; norm_num)
  have hLN : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    centralizer_le_normalizer_of_three_dvd h.toSec14Std h3
  have hcL : c ∉ L := h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  have hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L) :=
    eq_sup_of_card_nine hD h9 fun hc => hcL hc.2
  set S := A ⊓ L with hS
  set Q := CFSG.Open.pCoreOf 2 L with hQ
  set CB := Subgroup.centralizer (B : Set G) with hCB
  set T := Q ⊓ CB with hT
  have hBA : B ≤ A := hB.1
  have hB9 : Nat.card B = 9 := by
    have := hB.2
    rw [hD.card_eq] at this
    omega
  have hAA : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hA.1
  have hAB : A ≤ CB := hAA.trans (Subgroup.centralizer_le hBA)
  obtain ⟨b, hbB, hbS, hb1⟩ :=
    exists_mem_inf_ne_one hA.1 hD.card_eq hBA hB9 inf_le_left h9
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) :=
    hD.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hAQ ha, Subgroup.le_normalizer (hAB ha)⟩
  have hST : S ≤ Subgroup.normalizer (T : Set G) := inf_le_left.trans hAT
  have hT2 : IsPGroup 2 T := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le inf_le_left
  have hT3 : ¬ 3 ∣ Nat.card T := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT2
    rw [hn]
    intro h3'
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3')
    omega
  have hSTbot : S ⊓ T = ⊥ := inf_eq_bot_of_coprime (isPGroup_of_card_nine h9) hT3
  have hMcard : Nat.card (S ⊔ T : Subgroup G) = 9 * Nat.card T := by
    have := Sec6.card_sup_mul_card_inf hST
    rw [hSTbot, Subgroup.card_bot, mul_one, h9] at this
    exact this
  have hsyl : ∀ X : Subgroup G, X ≤ S ⊔ T → Nat.card X = 9 →
      CFSG.ABGLocalTools.IsSylowOf 3 X (S ⊔ T) := by
    intro X hXM hX9
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hXM, isPGroup_of_card_nine hX9, ?_⟩
    have h1 := Subgroup.relIndex_mul_card X (S ⊔ T)
    rw [inf_eq_left.mpr hXM, hX9, hMcard] at h1
    have h2 : X.relIndex (S ⊔ T) = Nat.card T := by omega
    rw [h2]
    exact hT3
  have hQN : S ≤ Subgroup.normalizer (Q : Set G) := inf_le_left.trans hAQ
  intro x hx
  have hxc : x ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcB) hx
  have hxL : x ∈ Subgroup.normalizer (L : Set G) := hLN hxc
  set Sx := S.map (MulAut.conj x).toMonoidHom with hSx
  have hSx9 : Nat.card Sx = 9 := by
    rw [hSx, Subgroup.card_map_of_injective (MulAut.conj x).injective, h9]
  have hSxL : Sx ≤ L := by
    rintro _ ⟨s, hs, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hxL s).mp hs.2
  have hSxB : Sx ≤ CB := by
    rintro _ ⟨s, hs, rfl⟩
    exact CB.mul_mem (CB.mul_mem hx (hAB hs.1)) (CB.inv_mem hx)
  have hSxM : Sx ≤ S ⊔ T := by
    intro y hy
    have hy' := inf_centralizer_le_sup_theta inf_le_right h9 χ hbS hb1
      ⟨hSxL hy, Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB) (hSxB hy)⟩
    rw [hθQ, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right S Q hQN] at hy'
    obtain ⟨s, hs, t, ht, rfl⟩ := hy'
    have htB : t ∈ CB := by
      have := CB.mul_mem (CB.inv_mem (hAB hs.1)) (hSxB hy)
      simpa using this
    exact Subgroup.mul_mem_sup hs ⟨ht, htB⟩
  obtain ⟨k, hkM, hk⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj (hsyl S le_sup_left h9)
    (hsyl Sx hSxM hSx9)
  rw [sup_comm, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left T S hST] at hkM
  obtain ⟨t, ht, s, hs, rfl⟩ := hkM
  have hn : t⁻¹ * x ∈ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have h1 : x * g * x⁻¹ ∈ Sx ↔ g ∈ S := by
      constructor
      · rintro ⟨g', hg', hgg'⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hgg'
        have hg : g' = g := by
          have := congrArg (fun z => x⁻¹ * z * x) hgg'
          simpa [mul_assoc] using this
        rwa [← hg]
      · intro hg
        exact ⟨g, hg, rfl⟩
    have h2 : (t * s)⁻¹ * (x * g * x⁻¹) * (t * s) =
        s⁻¹ * (t⁻¹ * x * g * (t⁻¹ * x)⁻¹) * s := by group
    have h3 : s⁻¹ * (t⁻¹ * x * g * (t⁻¹ * x)⁻¹) * s ∈ S ↔ t⁻¹ * x * g * (t⁻¹ * x)⁻¹ ∈ S := by
      constructor
      · intro hm
        have := S.mul_mem (S.mul_mem hs hm) (S.inv_mem hs)
        have h4 : s * (s⁻¹ * (t⁻¹ * x * g * (t⁻¹ * x)⁻¹) * s) * s⁻¹ =
            t⁻¹ * x * g * (t⁻¹ * x)⁻¹ := by group
        rwa [h4] at this
      · intro hm
        exact S.mul_mem (S.mul_mem (S.inv_mem hs) hm) hs
    rw [← h1, hk, h2, h3]
  have hnB : t⁻¹ * x ∈ CB := CB.mul_mem (CB.inv_mem ht.2) hx
  have hnc : t⁻¹ * x ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    centralizer_le_normalizer_zpowers c
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcB) hnB)
  have hnA : t⁻¹ * x ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    conv_lhs => rw [hAeq]
    rw [Subgroup.map_sup, Subgroup.mem_normalizer_iff_map_conj_eq.mp hnc,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hn, ← hAeq]
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 3
    Nat.prime_three A T (IsPGroup.of_card (n := 3) (by rw [hD.card_eq]; norm_num)) hAT
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hT3)
  have htT : t ∈ Subgroup.normalizer (A : Set G) ⊔ ⁅T, A⁆ := by
    have hle : ⁅T, A⁆ ⊔ T ⊓ Subgroup.centralizer (A : Set G) ≤
        Subgroup.normalizer (A : Set G) ⊔ ⁅T, A⁆ :=
      sup_le le_sup_right
        (le_sup_of_le_left (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)))
    have ht' : t ∈ ⁅T, A⁆ ⊔ T ⊓ Subgroup.centralizer (A : Set G) := by
      rw [hfac]
      exact ht
    exact hle ht'
  have hxt : x = t * (t⁻¹ * x) := by group
  rw [hxt]
  exact Subgroup.mul_mem _ htT (le_sup_left (a := Subgroup.normalizer (A : Set G)) hnA)

end Proof1510Steps

open Proof1510Steps

theorem step1510Plane_of
    (hset : Item13SetupAt) : Step1510Plane := by
  intro G _ _ A c L h hall E hEA _ e heE _ heΩ
  obtain ⟨Le, hLe⟩ := hset G h.toPartTwoStanding h.partTwoS_eq A h.mem_partTwoF
    h.not_mem_partTwoT e heΩ
  exact commutator_theta_le_of_point (Proof1511.sec15R_point h heΩ hLe) (hall e Le hLe heΩ) hEA
    heE

theorem step1510Cent_of :
    Step1510Cent := by
  intro G _ _ A c L h hall B hB hcB _
  exact centralizer_le_sup_of_point h (hall c L h.mem_lA h.zpowers_mem_omegaA) hB hcB

end CFSG.RankThree.PartTwo.Sec15
