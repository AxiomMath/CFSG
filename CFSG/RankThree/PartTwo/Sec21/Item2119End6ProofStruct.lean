module

public import CFSG.RankThree.PartTwo.Sec21.Item2119End5Proof2127C
import CFSG.RankThree.PartTwo.Sec21.Item2119End6ProofTools
import CFSG.RankThree.PartTwo.KFacts.L34Aut
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.PartTwo.Sec21.Item21Late2ProofFrame
import CFSG.RankThree.PartTwo.Sec21.Item21Late2Proof2120
import CFSG.RankThree.PartTwo.Sec21.Item21LateProofGL33
import CFSG.RankThree.PartTwo.Sec21.Item21Early2ProofModels
import CFSG.RankThree.PartTwo.Sec21.Item2119End3Proof2123
import CFSG.RankThree.PartTwo.Sec21.Item2119End3Proof2125Unique
import CFSG.RankThree.PartTwo.Sec21.Item2119End4Proof2125
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.GroupTheory.SteinbergBYCentralCoverRank
import CFSG.RankThree.Asc83Table.E27
import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartOne.S12.ModelTransport
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalRelative
public import CFSG.RankThree.PartTwo.Late.GammaZero
public import CFSG.RankThree.PartTwo.Sec11.Item118
public import CFSG.RankThree.PartTwo.Sec11.Item119
public import CFSG.RankThree.PartTwo.Sec13.Item135
public import CFSG.RankThree.PartTwo.Sec13.Item135Simple
public import CFSG.RankThree.PartTwo.Sec13.Item135SimpleReduce
public import CFSG.RankThree.PartTwo.Sec18.Notation
public import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.RankThree.PartTwo.Sec21.Commute33
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofHeis
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
public import CFSG.RankThree.PartTwo.Sec21.Item21Late2ProofAssembly
public import CFSG.RankThree.PartTwo.Sec21.Item21Late2ProofChoiceY
public import CFSG.RankThree.PartTwo.Sec21.Item21LateProofChoice
public import CFSG.RankThree.PartTwo.Sec21.Item21Res6ProofNoField
public import CFSG.RankThree.PartTwo.Sec21.Item221Proof228Statements
public import CFSG.RankThree.PartTwo.Sec21.Item221ProofZGen
public import CFSG.RankThree.PartTwo.Sec21.Item223Gaps
public import CFSG.RankThree.PartTwo.Sec21.Item229Diagram
public import CFSG.RankThree.PartTwo.Sec21.Item233
public import CFSG.RankThree.PartTwo.Sec21.Item233OneProof
public import CFSG.RankThree.PartTwo.Sec21.SylowThree
public import CFSG.RankThree.PartTwo.Sec4.Item47
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.Statements423
public import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.Sporadic.Schreier.RuSylow
public import Certificates.Certificate2195
public import Certificates.Certificate3157
public import Certificates.Certificate3164
public import Certificates.Certificate7233Base

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)

namespace Item2119End6Proof

variable {G : Type} [Group G] [Finite G]

theorem card_autThetaQuot_eq {L S : Subgroup G} (hSN : S ≤ Subgroup.normalizer (L : Set G))
    (hS : ∀ s ∈ S, s ∈ Sec4.thetaQuotCentralizer L → s = 1) :
    Nat.card (Sec4.autThetaQuot S L) = Nat.card S := by
  set ψ : S →* MulAut (lBar L) :=
    ((Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom).comp (Subgroup.inclusion hSN) with hψ
  have hrange : ψ.range = Sec4.autThetaQuot S L := by
    ext τ
    constructor
    · rintro ⟨s, rfl⟩
      exact Sec4.mem_autThetaQuot_iff.mpr ⟨s, hSN s.2, s.2, rfl⟩
    · intro hτ
      obtain ⟨h, hN, hhS, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
      exact ⟨⟨h, hhS⟩, rfl⟩
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have hsC : (s : G) ∈ Sec4.thetaQuotCentralizer L :=
      ⟨Subgroup.inclusion hSN s, MonoidHom.mem_ker.mpr hs, rfl⟩
    exact Subtype.ext (hS s s.2 hsC)
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]

theorem isElementaryAbelian_autThetaQuot {L F : Subgroup G} (hFe : IsElemAbelian 3 F) :
    CFSG.IsElementaryAbelian 3 (Sec4.autThetaQuot F L) := by
  have hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set T : Subgroup.normalizer (L : Set G) →* MulAut (lBar L) :=
    (Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom with hT
  refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩, exponent_dvd_p := ?_ }
  · obtain ⟨h, hN, hhF, hx⟩ := Sec4.mem_autThetaQuot_iff.mp x.2
    obtain ⟨h', hN', hh'F, hy⟩ := Sec4.mem_autThetaQuot_iff.mp y.2
    apply Subtype.ext
    change (x : MulAut (lBar L)) * y = y * x
    have hx' : T ⟨h, hN⟩ = x := hx
    have hy' : T ⟨h', hN'⟩ = y := hy
    rw [← hx', ← hy', ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hFc h hhF h' hh'F)
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
    obtain ⟨h, hN, hhF, hx⟩ := Sec4.mem_autThetaQuot_iff.mp x.2
    have hx' : T ⟨h, hN⟩ = x := hx
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hx', ← map_pow]
    rw [show (⟨h, hN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 from
      Subtype.ext (by simpa using hFe.2 h hhF), map_one]

theorem card_le_nine_of_isElementaryAbelian {L : Subgroup G}
    (eL : lBar L ≃* projSL 3 (GaloisField 2 2)) {X : Subgroup (MulAut (lBar L))}
    (hX : CFSG.IsElementaryAbelian 3 X) : Nat.card X ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut (lBar L)) :=
    Finite.of_injective (fun σ : MulAut (lBar L) => (σ : lBar L → lBar L))
      DFunLike.coe_injective
  obtain ⟨k, hk⟩ := (@CFSG.IsElementaryAbelian.isPGroup 3 X _ hX).exists_card_eq
  have hk2 : k ≤ 2 := by
    have h := CFSG.RankThree.GroupTheory.SteinbergBY.le_pRank_of_elementaryAbelian_card
      (by norm_num) hX hk
    rwa [CFSG.RankThree.Asc83Table.pRank_congr (MulAut.congr eL),
      KFacts.L34.pRank_three_mulAut_projSL] at h
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 9 := by norm_num

end Item2119End6Proof

open Item2119End6Proof

theorem item2127Struct_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) : Item2127Struct := by
  intro G _ _ A E U c L d hP F hF
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcfg := hP.cfg
  have hpair := hcfg.pair
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hmax : ∀ B : Subgroup G, IsElemAbelian 3 B → A ≤ B → B = A := hpair.mem_S.1.2.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have h27A : Nat.card A = 27 := by rw [hcfg.card]; norm_num
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hc3 : c ^ 3 = 1 := h3 c hcA
  have hdA : d ∈ A := hP.mem_d.1
  have hdL : d ∈ L := hP.mem_d.2
  have hd1 := hP.ne_one_d
  have hd3 : d ^ 3 = 1 := h3 d hdA
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hpairs.2.2.1
  have hG4 := hpair.standing.toTheoremFourHyp
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG4 hAe hcA hc1 L hLc
  have hcL : c ∉ L := (Item21Late2Proof.frame_of h45 h66 hcfg).1
  have hcd : c ∉ Subgroup.zpowers d := fun h => hcL ((Subgroup.zpowers_le.mpr hdL) h)
  have hdc : d ∉ Subgroup.zpowers c := Item2119End4Proof.not_mem_zpowers_symm hc3 hd1 hcd
  obtain ⟨eL⟩ := hP.l34
  have hLs : L ∈ lStar A :=
    lZeroStar_subset_lStar A (lZeroStarAt_subset_lZeroStar A c hpairs.2.2.1)
  have hCA : A ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr
      ⟨hcA, Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hLc⟩) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
    exact Sec6.card_le_three_of_isCyclic (h66 G hpair.standing A hpair.mem_S L hLs)
      fun y hy => h3 y hy.1
  have hZ : Subgroup.center (lBar L) = ⊥ :=
    Item2119End3Proof.center_eq_bot_of_mulEquiv' eL
      (Item21Early2Proof.center_projSL_three_eq_bot (by norm_num) (by decide))
  obtain ⟨hFe, hF27, hFAL, hAF, ⟨eQ⟩⟩ := hF
  have hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hF3 : ∀ x ∈ F, x ^ 3 = 1 := hFe.2
  have hALN : A ⊔ L ≤ Subgroup.normalizer (L : Set G) := sup_le hAL Subgroup.le_normalizer
  have hFN : F ≤ Subgroup.normalizer (L : Set G) := hFAL.trans hALN
  set S := F ⊓ L with hSdef
  have hS3 : IsPGroup 3 S := fun x => ⟨1, Subtype.ext (by simpa using hF3 x x.2.1)⟩
  have hSdvd : Nat.card S ∣ 9 := card_dvd_nine_of_le eL inf_le_right hS3
  have hSnot3 : ¬ Nat.card S ∣ 3 := by
    intro hS3'
    set σ := eQ.symm (QuaternionGroup.a 1) with hσ
    have hσ4 : orderOf (σ : MulAut F) = 4 := by
      rw [Subgroup.orderOf_coe, hσ, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_a_one]
    obtain ⟨l, hlN, hlL, hσl⟩ := Sec4.mem_autIn_iff.mp σ.2
    set M : Subgroup F := S.subgroupOf F with hM
    have hMcard : Nat.card M = Nat.card S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : S ≤ F)).toEquiv
    have hφ : ∀ x : F, x⁻¹ * (σ : MulAut F) x ∈ M := by
      intro x
      rw [hM, Subgroup.mem_subgroupOf]
      have hx : ((σ : MulAut F) x : G) = l * x * l⁻¹ := by
        rw [← hσl]
        rfl
      have hxN : (x : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) := inv_mem (hFN x.2)
      refine ⟨Subgroup.mul_mem _ (inv_mem x.2) ((σ : MulAut F) x).2, ?_⟩
      change (x : G)⁻¹ * ((σ : MulAut F) x : G) ∈ L
      rw [hx]
      have h1 : (x : G)⁻¹ * l * (x : G)⁻¹⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp hxN l).mp hlL
      have h2 := L.mul_mem h1 (inv_mem hlL)
      rwa [show (x : G)⁻¹ * l * (x : G)⁻¹⁻¹ * l⁻¹ = (x : G)⁻¹ * (l * x * l⁻¹) by group] at h2
    have h6 := pow_six_eq_one_of_forall_inv_mul_mem (P := F)
      (fun x => Subtype.ext (by simpa using hF3 x x.2)) (hMcard ▸ hS3') hφ
    have h46 : (4 : ℕ) ∣ 6 := hσ4 ▸ orderOf_dvd_of_pow_eq_one h6
    omega
  have hS9 : Nat.card S = 9 := by
    obtain ⟨j, hj, hjS⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (show Nat.card S ∣ 3 ^ 2 by norm_num; exact hSdvd)
    interval_cases j
    · exact absurd (by rw [hjS]; norm_num) hSnot3
    · exact absurd (by rw [hjS]; norm_num) hSnot3
    · rw [hjS]; norm_num
  have hdNS : d ∈ Subgroup.normalizer (S : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hAF hdA, hAL hdA⟩
  have hzd3 : IsPGroup 3 (Subgroup.zpowers d) := by
    rintro ⟨g, n, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one, pow_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3, one_zpow]
  have hSd3 : IsPGroup 3 (S ⊔ Subgroup.zpowers d : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hS3 hzd3 (Subgroup.zpowers_le.mpr hdNS)
  have hSdL : S ⊔ Subgroup.zpowers d ≤ L := sup_le inf_le_right (Subgroup.zpowers_le.mpr hdL)
  have hSeq : S = S ⊔ Subgroup.zpowers d := Subgroup.eq_of_le_of_card_ge le_sup_left
    (by rw [hS9]; exact Nat.le_of_dvd (by norm_num) (card_dvd_nine_of_le eL hSdL hSd3))
  have hdS : d ∈ S := by
    rw [hSeq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
  have hdF : d ∈ F := hdS.1
  have hKF : F ⊓ Sec4.thetaQuotCentralizer L ≠ ⊥ := by
    intro hbot
    have hcard := card_autThetaQuot_eq hFN (fun s hs hsC => by
      have : s ∈ F ⊓ Sec4.thetaQuotCentralizer L := ⟨hs, hsC⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact this)
    have hle := card_le_nine_of_isElementaryAbelian eL (isElementaryAbelian_autThetaQuot (L := L)
      hFe)
    rw [hcard, hF27] at hle
    norm_num at hle
  have hAK : A ≤ Subgroup.normalizer ((F ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) : Set G) :=
    fun a ha => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hAF ha, Sec6.normalizer_le_normalizer_thetaQuotCentralizer L (hAL ha)⟩
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using h3 x x.2)⟩
  have hK3 : IsPGroup 3 (F ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) :=
    fun x => ⟨1, Subtype.ext (by simpa using hF3 x x.2.1)⟩
  obtain ⟨y, hyK, hy1, hyA⟩ := exists_ne_one_fixed hA3 hK3 hKF hAK
  have hy3 : y ^ 3 = 1 := hF3 y hyK.1
  have hyAc : ∀ b ∈ A, y * b = b * y := fun b hb => by
    have h := hyA b hb
    calc y * b = b * (b⁻¹ * y * b) := by group
      _ = b * y := by
          rw [show b⁻¹ * y * b = y by
            calc b⁻¹ * y * b = b⁻¹ * (b * y * b⁻¹) * b := by rw [h]
              _ = y := by group]
  have hyA' : y ∈ A := by
    obtain ⟨hAy, -⟩ := Item2119End3Proof.isElemAbelian_sup_zpowers hAe hy3 hyAc
    have heq := hmax _ hAy le_sup_left
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hyc : y ∈ Subgroup.zpowers c := by
    rw [← hCA]
    exact ⟨hyA', hyK.2⟩
  have hcy : c ∈ Subgroup.zpowers y :=
    Item21Late2Proof.mem_zpowers_of_mem hc3 hyc hy1 (Subgroup.mem_zpowers c)
  have hcF : c ∈ F := (Subgroup.zpowers_le.mpr hyK.1) hcy
  set M := Subgroup.zpowers c ⊔ Subgroup.zpowers d with hMdef
  have hM9 : Nat.card M = 9 :=
    Item21LateProof.card_zpowers_sup_zpowers (hcomm c hcA d hdA) hc3 hd3 hc1 hdc
  have hMF : M ≤ F := sup_le (Subgroup.zpowers_le.mpr hcF) (Subgroup.zpowers_le.mpr hdF)
  have hMA : M ≤ A := sup_le (Subgroup.zpowers_le.mpr hcA) (Subgroup.zpowers_le.mpr hdA)
  have hexp : ∀ x ∈ A ⊔ F, x ^ 3 = 1 := by
    intro x hx
    have hx' : x ∈ ((A ⊔ F : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A F hAF] at hx'
    obtain ⟨a, ha, f, hf, rfl⟩ := hx'
    exact pow_three_mul_eq_one hFe hF27 hMF hM9 (h3 a ha) (hAF ha)
      (fun m hm => by rw [hcomm a ha m (hMA hm), mul_inv_cancel_right]) hf
  refine ⟨hexp, hdF, ?_⟩
  have hP₀3 : IsPGroup 3 (A ⊔ F : Subgroup G) :=
    fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩
  have hup : Nat.card (Sec4.autThetaQuot (A ⊔ F) L) ≤ 27 :=
    Item2119End5Proof.card_autThetaQuot_le eL hP₀3
  have hpg : IsPGroup 3 (Sec4.autThetaQuot (A ⊔ F) L) :=
    (((hP₀3.to_le inf_le_left).comap_subtype).map _).map _
  have hSC : ∀ s ∈ S, s ∈ Sec4.thetaQuotCentralizer L → s = 1 := fun s hs hsC =>
    Item2119End3Proof.eq_one_of_mem_thetaQuotCentralizer hZ hs.2 hsC (hF3 s hs.1)
  have hS9' : Nat.card (Sec4.autThetaQuot S L) = 9 := by
    rw [card_autThetaQuot_eq (inf_le_left.trans hFN) hSC, hS9]
  have hSle : Sec4.autThetaQuot S L ≤ Sec4.autThetaQuot (A ⊔ F) L := by
    intro τ hτ
    obtain ⟨h, hN, hhS, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
    exact Sec4.mem_autThetaQuot_iff.mpr ⟨h, hN, Subgroup.mem_sup_right hhS.1, rfl⟩
  obtain ⟨e, heA, heM⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hMA (fun h => by
    rw [h, h27A] at hM9
    norm_num at hM9))
  have he1 : e ≠ 1 := fun h => heM (h ▸ M.one_mem)
  have hed : e ∉ Subgroup.zpowers d := fun h => heM (Subgroup.mem_sup_right h)
  have heDC : e ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers c := by
    rw [sup_comm]
    exact heM
  have hcDE : c ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers e :=
    Item2119End4Proof.not_mem_sup_swap (hcomm d hdA c hcA) (hcomm d hdA e heA) hd3 hc3
      (h3 e heA) hd1 hcd heDC
  have hcED : c ∉ Subgroup.zpowers e ⊔ Subgroup.zpowers d := by
    rw [sup_comm]
    exact hcDE
  have heT : Sec4.InducesTypeOn L e 2 :=
    Item2119End3Proof.inducesTypeOn_two_gen h45 h66 heA he1 hdA hd1 hed hcfg hdL hP.type_d hcED
  have heAF : Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨e, hAL heA⟩) ∈
      Sec4.autThetaQuot (A ⊔ F) L :=
    Sec4.mem_autThetaQuot_iff.mpr ⟨e, hAL heA, Subgroup.mem_sup_left heA, rfl⟩
  have heS : Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨e, hAL heA⟩) ∉
      Sec4.autThetaQuot S L := by
    intro hmem
    obtain ⟨h, hN, hhS, hh⟩ := Sec4.mem_autThetaQuot_iff.mp hmem
    refine not_inner_of_inducesTypeOn_two eL heT (hAL heA) ((⟨h, hhS.2⟩ : L) : lBar L)
      fun z => ?_
    rw [← hh]
    exact Item21Late2Proof.thetaQuotMulAut_inner hhS.2 hN z
  have hlt : Sec4.autThetaQuot S L < Sec4.autThetaQuot (A ⊔ F) L :=
    lt_of_le_of_ne hSle (fun h => heS (h ▸ heAF))
  have hgt : 9 < Nat.card (Sec4.autThetaQuot (A ⊔ F) L) := by
    rw [← hS9']
    exact Subgroup.card_lt_of_lt hlt
  obtain ⟨k, hk⟩ := hpg.exists_card_eq
  rw [hk] at hup hgt ⊢
  have hk3 : k ≤ 3 := by
    by_contra h
    have : 3 ^ 4 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> first | rfl | (exfalso; norm_num at hgt)

end CFSG.RankThree.PartTwo.Sec21
