module

public import CFSG.RankThree.PartTwo.Sec15.Item1513Res2ProofEven
import CFSG.RankThree.PartTwo.Sec15.Item1513Res3ProofTransOut
import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofTools
import CFSG.RankThree.PartTwo.Sec17.Item17Q0ProofTools
import CFSG.Goldschmidt.Steps.G310Basic
public import Certificates.Certificate3029
public import Certificates.Certificate3086
public import Certificates.Certificate3139
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThreeBasic
import CFSG.RankThree.PartTwo.Sec15.Item1513ProofTools
import CFSG.RankThree.PartTwo.Sec15.Item1513ProofNoTransv
import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofTransv
import CFSG.RankThree.PartTwo.Sec15.Item1511ProofTools
import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofPoints
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13GL
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec13.Item134Sylow
import CFSG.RankThree.PartTwo.KFacts.K74Plane
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJSLTools
import CFSG.RankThree.PartTwo.Sec8.Hering611S3App
import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofFrattini
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThreeM12
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThreeSylow
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
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
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartTwo.KFacts.KS12MovesSL
import CFSG.RankThree.PartTwo.Sec11.Item111
import CFSG.RankThree.PartTwo.Sec12.Item125DiagBasic
import CFSG.RankThree.PartTwo.Sec12.Item128BarProofStatements
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJSLStatements
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJStatements
import CFSG.RankThree.PartTwo.Sec15.NoModNine
import CFSG.RankThree.PartTwo.Sec4.Census.Interface46
import CFSG.RankThree.PartTwo.Sec4.Item47Diag
import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.Item47Witness
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec8.Hering611S3KBase
import CFSG.RankThree.PartTwo.Sec8.Hering611SImg2
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

namespace Sylow1513M12

open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree in
theorem real3_nativeM12 : Real3 CFSG.Blueprint.NativeSporadic.M12 := by
  have : Finite CFSG.Blueprint.NativeSporadic.M12 :=
    Nat.finite_of_card_ne_zero (by rw [KFacts.KS14.card_nativeM12]; norm_num)
  exact real3_of_gen m12_gen_facts.1 m12_gen_facts.2 m12f m12σx m12σy m12f_inj m12f_mem
    m12f_one m12f_σx m12f_σy 3 (by simp) (by rw [KFacts.KS14.card_nativeM12]; norm_num)
    fun p => ⟨m12t p, m12f_tinv p⟩

open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree in
theorem exists_inv_conj_of_real3 {K : Type*} [Group K] [Finite K]
    (hR : Real3 (K ⧸ aschbacherSolvableCore 3 K)) {z : K} (hz : z ^ 3 = 1) :
    ∃ t : K, t * z * t⁻¹ = z⁻¹ := by
  obtain ⟨s, hs⟩ := hR (z : K ⧸ aschbacherSolvableCore 3 K) (by
    rw [← QuotientGroup.mk_pow, hz, QuotientGroup.mk_one])
  obtain ⟨t₀, rfl⟩ := QuotientGroup.mk_surjective s
  have hN3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 K) :=
    (solvable_prime_complement_core_characterization (H := K) Nat.prime_three).2.2.1
  have hmem : (z⁻¹)⁻¹ * (t₀ * z * t₀⁻¹) ∈ aschbacherSolvableCore 3 K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      inv_inv, hs, mul_inv_cancel]
  have hz' : z⁻¹ ^ 3 = 1 := by rw [inv_pow, hz, inv_one]
  have hy3 : (t₀ * z * t₀⁻¹) ^ 3 = 1 := by rw [conj_pow, hz, mul_one, mul_inv_cancel]
  obtain ⟨u, -, hu⟩ := Sec8.Item812Res3.exists_mem_conj_eq_of_inv_mul_mem hN3 hz' hy3 hmem
  exact ⟨u * t₀, by rw [← hu]; group⟩

variable {G : Type} [Group G] [Finite G]

theorem exists_inv_of_irreducible {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hirr : Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L))) :
    ∃ j ∈ L, ∀ b ∈ A ⊓ L, j * b * j⁻¹ = b⁻¹ := by
  have h4 := KFacts.four_dvd_card_of_isIrreducibleOn (Proof1513.isElemAbelian_inf hD) h9 hirr
  obtain ⟨ι, hι, hιinv⟩ := Sec13.exists_inv_mem_of_four_dvd (Proof1513.isElemAbelian_inf hD) h9 h4
  obtain ⟨j, hjN, hjH, rfl⟩ := Sec4.mem_autIn_iff.mp hι
  refine ⟨j, hjH.1, fun b hb => ?_⟩
  have h1 := congrArg Subtype.val (hιinv ⟨b, hb⟩)
  rw [Sec4.normalizerMonoidHom_apply_coe] at h1
  simpa using h1

theorem false_of_m12
    (h131 : Item131) {A L K : Subgroup G} {c a : G}
    (hctx : Ctx1513 G A c L a K) {w : G} (hwKW : w ∈ K ⊓ Subgroup.normalizer (A : Set G))
    (hw3 : w ^ 3 = 1)
    (hwC9 : Nat.card (A ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) = 9)
    (e12 : lBarA a K A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := hctx.toSec15R
  have hD := h.toSec13Data
  have hDa := (Proof1511.sec15R_point h hctx.zpowers_a_mem hctx.mem_lA_a).toSec13Data
  have h9 := hctx.card_inf
  have hirr := hctx.irreducible
  have hcL : c ∉ L := h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  obtain ⟨-, htypes⟩ := Proof1513.cases_of_irreducible h131 h h9 hirr
  obtain ⟨-, ⟨hM12p, hM12z⟩, -⟩ := sporadicModels131
  obtain ⟨haK, -, -, ⟨ψK⟩⟩ := facts_of_prod hDa hM12p hM12z e12
  have hA := hD.isElemAbelian
  have hc3 : c ^ 3 = 1 := hA.2 c hD.mem_A
  have haA : a ∈ A := hDa.mem_A
  have hwK : w ∈ K := hwKW.1
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := hwKW.2
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := hDa.le_normalizer
  have hwc : w * c * w⁻¹ = c :=
    Proof1513.commute_of_mem_normalizer_zpowers hc3 hD.ne_one (hctx.normalizer_le hwA) hw3
  have hcw : c * w = w * c := by
    calc c * w = w * c * w⁻¹ * w := by rw [hwc]
      _ = w * c := by group
  have hwCc : w ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcw.symm
  have huniq := (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).2
  have h3L : 3 ∣ Nat.card L :=
    (show 3 ∣ 9 by norm_num).trans (h9 ▸ Subgroup.card_dvd_of_le inf_le_right)
  have hwL : w ∈ Subgroup.normalizer (L : Set G) := by
    have hmem := Sec13.conj_mem_thetaComponentsAt_of_mem_centralizer hwCc hD.mem_thetaComponentsAt
    have hcard : 3 ∣ Nat.card (L.map (MulAut.conj w).toMonoidHom) := by
      rwa [Subgroup.card_map_of_injective (MulAut.conj w).injective]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (huniq _ hmem hcard)
  obtain ⟨x, hxAL, hxw⟩ : ∃ x ∈ A ⊓ L, x * w ≠ w * x := by
    by_contra hall
    push Not at hall
    have hAle : A ≤ Subgroup.centralizer ({w} : Set G) := by
      refine (le_of_eq (Sec13.eq_sup_of_card_nine hD h9 fun h1 => hcL h1.2)).trans
        (sup_le (Subgroup.zpowers_le.mpr ?_) fun y hy => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hcw
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hall y hy)
    rw [inf_of_le_left hAle, hD.card_eq] at hwC9
    norm_num at hwC9
  set f₀ := x * w * x⁻¹ * w⁻¹ with hf₀
  have hf₀K : f₀ ∈ K :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp (hAK hxAL.1) w).mp hwK) (inv_mem hwK)
  have hf₀A : f₀ ∈ A := by
    have h1 : w * x⁻¹ * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hwA x⁻¹).mp (inv_mem hxAL.1)
    have e : f₀ = x * (w * x⁻¹ * w⁻¹) := by rw [hf₀]; group
    rw [e]
    exact mul_mem hxAL.1 h1
  have hf₀L : f₀ ∈ L := by
    have h1 : w * x⁻¹ * w⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hwL x⁻¹).mp (inv_mem hxAL.2)
    have e : f₀ = x * (w * x⁻¹ * w⁻¹) := by rw [hf₀]; group
    rw [e]
    exact mul_mem hxAL.2 h1
  have hf₀1 : f₀ ≠ 1 := by
    intro h1
    apply hxw
    have h2 : x * w * x⁻¹ = w := by rw [← mul_inv_eq_one]; exact h1
    calc x * w = x * w * x⁻¹ * x := by group
      _ = w * x := by rw [h2]
  set D := A ⊓ L ⊓ K with hDdef
  have hDne : D ≠ ⊥ := by
    intro hbot
    apply hf₀1
    have : f₀ ∈ D := ⟨⟨hf₀A, hf₀L⟩, hf₀K⟩
    rwa [hbot, Subgroup.mem_bot] at this
  have hwD : w ∈ Subgroup.normalizer (D : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.inf_normalizer_le_normalizer_inf ⟨hwA, hwL⟩, Subgroup.le_normalizer hwK⟩
  have hD3 : IsPGroup 3 D := fun g => ⟨1, Subtype.ext (by simpa using hA.2 _ g.2.1.1)⟩
  set Q := Subgroup.zpowers w ⊔ D with hQ
  have hQ3 : IsPGroup 3 Q := IsPGroup.to_sup_of_normal_right'
    (Proof1513Steps.isPGroup_zpowers_of_pow_three hw3) hD3 (Subgroup.zpowers_le.mpr hwD)
  have hQD : Q ≤ Subgroup.normalizer (D : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hwD) Subgroup.le_normalizer
  have hQD' : Q ⊓ D ≠ ⊥ := by rwa [inf_eq_right.mpr le_sup_right]
  obtain ⟨z, hzQD, hz1, hzc⟩ := Proof1513Steps.exists_central_of_normal hQ3 hQD hQD'
  have hzD : z ∈ D := hzQD.2
  have hzw : w * z = z * w := hzc w (Subgroup.mem_sup_left (Subgroup.mem_zpowers w))
  have hz3 : orderOf z = 3 := orderOf_eq_prime (hA.2 z hzD.1.1) hz1
  have hco3 : orderOf c = 3 := hD.orderOf_eq
  have hdisj : Subgroup.zpowers z ⊓ Subgroup.zpowers c = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    by_contra hy1
    have hy3 : orderOf y = 3 := by
      have h1 : orderOf y ∣ 3 := hco3 ▸ orderOf_dvd_of_mem_zpowers hy.2
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) (by simpa using hy1)
      · exact h
    have hyc : Subgroup.zpowers y = Subgroup.zpowers c :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy.2)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hy3, hco3])
    apply hcL
    have hcy : c ∈ Subgroup.zpowers y := hyc ▸ Subgroup.mem_zpowers c
    exact (Subgroup.zpowers_le.mpr hzD.1.2) ((Subgroup.zpowers_le.mpr hy.1) hcy)
  have hzcN : Subgroup.zpowers z ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Set.mem_singleton_iff.mp hy]
    exact hD.commute hD.mem_A hzD.1.1
  have hE9 : Nat.card (Subgroup.zpowers z ⊔ Subgroup.zpowers c : Subgroup G) = 9 := by
    have h1 := Sec6.card_sup_mul_card_inf hzcN
    rw [hdisj, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hz3, hco3] at h1
    exact h1
  have hEle : Subgroup.zpowers z ⊔ Subgroup.zpowers c ≤
      A ⊓ Subgroup.centralizer ({w} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ⟨hzD.1.1, ?_⟩)
      (Subgroup.zpowers_le.mpr ⟨hD.mem_A, ?_⟩)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hzw.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hcw
  have hEeq : Subgroup.zpowers z ⊔ Subgroup.zpowers c = A ⊓ Subgroup.centralizer ({w} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hEle (by rw [hwC9, hE9])
  have haE : a ∈ A ⊓ Subgroup.centralizer ({w} : Set G) := by
    refine ⟨haA, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hDa.le_centralizer hwK)).symm
  have haZ : a ∈ ((Subgroup.zpowers z : Set G) * (Subgroup.zpowers c : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hzcN, SetLike.mem_coe, hEeq]
    exact haE
  obtain ⟨y, hy, d, hd, hyd⟩ := Set.mem_mul.mp haZ
  have hyD : y ∈ D := (Subgroup.zpowers_le.mpr hzD) hy
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [mul_one] at hyd
    exact haK (hyd ▸ hyD.2)
  have hR := CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree.Real3.of_mulEquiv ψK
    real3_nativeM12
  have hy3 : y ^ 3 = 1 := hA.2 y hyD.1.1
  obtain ⟨⟨t, htK⟩, ht'⟩ :=
    exists_inv_conj_of_real3 hR (z := ⟨y, hyD.2⟩) (Subtype.ext (by simpa using hy3))
  have hty : t * y * t⁻¹ = y⁻¹ := congrArg Subtype.val ht'
  have hta : t * a * t⁻¹ = a := by
    have h1 : t * a = a * t := Subgroup.mem_centralizer_singleton_iff.mp (hDa.le_centralizer htK)
    rw [h1, mul_inv_cancel_right]
  obtain ⟨j, hjL, hjinv⟩ := exists_inv_of_irreducible hD h9 hirr
  have hjy : j * y * j⁻¹ = y⁻¹ := hjinv y hyD.1
  have hjd : j * d * j⁻¹ = d := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    have hjc : j * c = c * j := Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hjL)
    rw [(Commute.zpow_right hjc k).eq, mul_inv_cancel_right]
  have hga : t * j * a * (t * j)⁻¹ = d := by
    have hja : j * a * j⁻¹ = y⁻¹ * d := by
      rw [← hyd]
      calc j * (y * d) * j⁻¹ = (j * y * j⁻¹) * (j * d * j⁻¹) := by group
        _ = y⁻¹ * d := by rw [hjy, hjd]
    have hd' : d = y⁻¹ * a := by rw [← hyd]; group
    calc t * j * a * (t * j)⁻¹ = t * (j * a * j⁻¹) * t⁻¹ := by group
      _ = t * (y⁻¹ * (y⁻¹ * a)) * t⁻¹ := by rw [hja, hd']
      _ = (t * y * t⁻¹)⁻¹ * (t * y * t⁻¹)⁻¹ * (t * a * t⁻¹) := by group
      _ = y * y * a := by rw [hty, hta, inv_inv]
      _ = y ^ 3 * d := by rw [← hyd, pow_three]; simp only [mul_assoc]
      _ = d := by rw [hy3, one_mul]
  have hdc : Subgroup.zpowers d = Subgroup.zpowers c := by
    have hd3 : orderOf d = 3 := by
      have h1 : orderOf d ∣ 3 := hco3 ▸ orderOf_dvd_of_mem_zpowers hd
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hd1
      · exact h1
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hd)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hd3, hco3])
  have hKg := Sec12.KS128NotHJSL.map_conj_mem_thetaComponentsAt Nat.prime_three
    hDa.mem_thetaComponentsAt (t * j)
  rw [hga, Proof1515.thetaComponentsAt_eq_of_zpowers_eq hdc] at hKg
  have h3K : 3 ∣ Nat.card (K.map (MulAut.conj (t * j)).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (t * j)).injective, ← hz3]
    exact Subgroup.orderOf_dvd_natCard K hzD.2
  have hKL := huniq _ hKg h3K
  have hχ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* ↥K ⧸ aschbacherSolvableCore 3 ↥K) :=
    hKL ▸ Sec8.Hering611.thetaQuot_conj_equiv K (t * j)
  obtain ⟨χ⟩ := hχ
  have ψ := χ.trans ψK
  rcases htypes with ⟨p, e, hp, -, hL3⟩ | ⟨⟨χ7⟩⟩ | ⟨⟨χ22⟩⟩
  · exact KFacts.KS14.not_isoLThreePi_M12 p e (Proof1511.isoLThreePi_of_mulEquiv ψ hL3)
  · exact (Proof1514.isEmpty_mulEquiv_M12_of_A7 χ7).false ψ
  · exact (Proof1514.isEmpty_mulEquiv_M12_of_M22 χ22).false ψ

end Sylow1513M12

theorem step1513EvenNotM12_of
    (h131 : Item131) : Step1513EvenNotM12 := by
  intro G _ _ A c L a K hctx w hwKW hw3 hwC9 _
  exact ⟨fun e12 => Sylow1513M12.false_of_m12 h131 hctx hwKW hw3 hwC9 e12⟩

end CFSG.RankThree.PartTwo.Sec15
