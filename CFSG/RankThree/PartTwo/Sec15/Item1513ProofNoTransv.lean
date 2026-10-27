module

public import CFSG.RankThree.PartTwo.Sec15.Item1513Proof
public import CFSG.RankThree.PartTwo.KFacts.KS18A7M22Proof
import CFSG.RankThree.PartTwo.Sec15.Item1511ProofTools
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item13Plane
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15.Proof1511
open CFSG.Assembly.RankThreeEven (projSL projSU projImage)

namespace Proof1513

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commute_of_mem_normalizer_zpowers {c w : G} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hw : w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)) (hw3 : w ^ 3 = 1) :
    w * c * w⁻¹ = c := by
  have hmem : w * c * w⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp hw c).mp (Subgroup.mem_zpowers c)
  rcases eq_of_mem_zpowers_of_pow_three hc3 hmem with h1 | h1 | h1
  · exfalso
    apply hc1
    have : c = w⁻¹ * (w * c * w⁻¹) * w := by group
    rw [this, h1]
    group
  · exact h1
  · exfalso
    have hpow : ∀ n : ℕ, w * c ^ n * w⁻¹ = (c ^ 2) ^ n := fun n => by
      rw [← conj_pow, h1]
    have h2 : w * (w * c * w⁻¹) * w⁻¹ = c := by
      rw [h1, hpow 2, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hc3, one_mul,
        pow_one]
    have hw3' : w * (w * w) = 1 := by rw [← pow_three, hw3]
    have h3 : w * (w * (w * c * w⁻¹) * w⁻¹) * w⁻¹ = c := by
      have : w * (w * (w * c * w⁻¹) * w⁻¹) * w⁻¹ = (w * (w * w)) * c * (w * (w * w))⁻¹ := by
        group
      rw [this, hw3']
      group
    rw [h2, h1] at h3
    apply hc1
    have h4 : c ^ 2 * c = c * c := by rw [h3]
    have h5 : c ^ 2 = c := mul_right_cancel h4
    have : c = c ^ 2 * c⁻¹ := by group
    rw [this, h5, mul_inv_cancel]

end Proof1513

open Proof1513


theorem step1513NoTransv_of (h131 : Item131) : Step1513NoTransv := by
  intro G _ _ A c L h hL w hw hw3 h9w
  have hD := h.toSec13Data
  have hcL : c ∉ L := h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  obtain ⟨-, hZ, hinn, -, hcomm3⟩ :=
    KFacts.KS14.ks18A7M22 (↥L ⧸ aschbacherSolvableCore 3 ↥L) hL.symm
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 := by
    rcases cases131 h131 sporadicModels131 slTwoCenter hD with ⟨-, h9, -⟩ | ⟨-, h9, -⟩ |
        ⟨-, -, -, x, -, hx⟩ | ⟨hcL', -⟩
    · exact h9
    · exact h9
    · exfalso
      obtain ⟨-, π, p, f, K, _, hK, hq, e, -⟩ := hx
      have hLL := isLThreePi_of_mulEquiv e (isLThreePi_projImage_slPi hK hq)
      rcases hL with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
      · exact not_isLThreePi_of_mulEquiv φ (fun p e _ => KFacts.KS14.not_isoLThreePi_M22 p e)
          hLL
      · exact not_isLThreePi_of_mulEquiv φ (fun p e _ => not_isoLThreePi_alternating_seven p e)
          hLL
    · exact (hcL hcL').elim
  obtain ⟨f, hfA, hfL, hfc⟩ := exists_mem_inf_not_mem_of_card_nine hD.card_zpowers h9
  have hwL : w ∈ Subgroup.normalizer (L : Set G) :=
    normalizer_inf_le_of_mem hD.mem_thetaComponentsAt hD.le_normalizer hD.sectionCentralizer_eq
      hfA hfL hfc hw
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := hw.2
  set σ := Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨w, hwL⟩) with hσ
  have hσ3 : σ ^ 3 = 1 := by
    have h1 : (⟨w, hwL⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hw3)
    rw [hσ, ← map_pow, ← map_pow, h1, map_one, map_one]
  obtain ⟨x, hx⟩ := hinn σ ⟨1, by rw [pow_one]; exact hσ3⟩
  have hx3 : x ^ 3 = 1 := by
    apply KFacts.KS14.conj_injective_of_center_eq_bot hZ
    rw [map_pow, ← hx, hσ3, map_one]
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  set E := ((A ⊓ L).subgroupOf L).map π with hE
  have hσE : ∀ y ∈ (A ⊓ L).subgroupOf L, σ (π y) = π ⟨w * y * w⁻¹,
      (Subgroup.mem_normalizer_iff.mp hwL y).mp y.2⟩ := fun y _ => rfl
  have hxE : Subgroup.zpowers x ≤ Subgroup.normalizer (E : Set _) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := hz
    have h1 : x * π y * x⁻¹ = σ (π y) := by rw [hx, MulAut.conj_apply]
    rw [h1, hσE y hy]
    refine ⟨_, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    have hyA : (y : G) ∈ A := (Subgroup.mem_subgroupOf.mp hy).1
    exact ⟨(Subgroup.mem_normalizer_iff.mp hwA _).mp hyA,
      (Subgroup.mem_normalizer_iff.mp hwL _).mp y.2⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3g : IsPGroup 3 (Subgroup.zpowers x) := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hx3) with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])
  have hE3 : IsPGroup 3 E := by
    refine IsPGroup.map ?_ π
    intro y
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    have hyA : ((y : ↥L) : G) ∈ A := (Subgroup.mem_subgroupOf.mp y.2).1
    simpa using hD.isElemAbelian.2 _ hyA
  have hQ := IsPGroup.to_sup_of_normal_right' hx3g hE3 hxE
  have hcomm := hcomm3 _ hQ
  have hfix : ∀ y ∈ (A ⊓ L).subgroupOf L, σ (π y) = π y := by
    intro y hy
    have hyE : π y ∈ Subgroup.zpowers x ⊔ E :=
      Subgroup.mem_sup_right ⟨y, hy, rfl⟩
    have hxQ : x ∈ Subgroup.zpowers x ⊔ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
    have hc := congrArg Subtype.val
      (hcomm.is_comm.comm (⟨x, hxQ⟩ : ↥(Subgroup.zpowers x ⊔ E)) ⟨π y, hyE⟩)
    simp only [Subgroup.coe_mul] at hc
    rw [hx, MulAut.conj_apply, hc, mul_inv_cancel_right]
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥L) :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
  have hcentAL : A ⊓ L ≤ Subgroup.centralizer ({w} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyL : (⟨y, hy.2⟩ : ↥L) ∈ (A ⊓ L).subgroupOf L := Subgroup.mem_subgroupOf.mpr hy
    have h1 := hfix _ hyL
    rw [hσE _ hyL, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at h1
    set u : ↥L := (⟨w * y * w⁻¹, (Subgroup.mem_normalizer_iff.mp hwL y).mp hy.2⟩ : ↥L)⁻¹ *
      ⟨y, hy.2⟩ with hu
    have huθ : u ∈ aschbacherSolvableCore 3 ↥L := h1
    have huA : (u : G) ∈ A := by
      rw [hu]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact A.mul_mem (A.inv_mem ((Subgroup.mem_normalizer_iff.mp hwA y).mp hy.1)) hy.1
    have hu3 : u ^ 3 = 1 := Subtype.ext (by simpa using hD.isElemAbelian.2 _ huA)
    have hu1 : u = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hu3) with h2 | h2
      · exact orderOf_eq_one_iff.mp h2
      · have hθdvd := Subgroup.orderOf_dvd_natCard _ huθ
        rw [h2] at hθdvd
        exact absurd hθdvd hθ3
    have h2 := congrArg Subtype.val hu1
    rw [hu] at h2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h2
    have h3 : w * y * w⁻¹ = y := inv_mul_eq_one.mp h2
    calc y * w = (w * y * w⁻¹) * w := by rw [h3]
      _ = w * y := by group
  have hwc : w * c * w⁻¹ = c :=
    commute_of_mem_normalizer_zpowers (hD.isElemAbelian.2 c hD.mem_A) hD.ne_one hw.1 hw3
  have hcC : Subgroup.zpowers c ≤ Subgroup.centralizer ({w} : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    calc c * w = (w * c * w⁻¹) * w := by rw [hwc]
      _ = w * c := by group
  have hAa := eq_sup_of_card_nine hD h9 (fun h1 => hcL h1.2)
  have hAC : A ≤ Subgroup.centralizer ({w} : Set G) := hAa ▸ sup_le hcC hcentAL
  have h27 : Nat.card (A ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) = 27 := by
    rw [inf_of_le_left hAC, hD.card_eq]
  omega

theorem item1513R_of_named (h131 : Item131) (h132 : Item132) (h133 : Item133)
    (hset : Item13SetupAt) (h159 : Item159R) (h1510 : Item1510R)
    (hBr : Sec16.Step169TwoBridge) (h1511 : Item1511StarR) (h1411 : Item1411_1R)
    (hloc : Claim1411LocalR) (h153 : Item153MainR) (hnorm : Claim153NormalR)
    (hHJ : Step1513HJ) (hmeets : Step1513Meets) (htv : Step1513Transv)
    (hmax : Step1513Max) (heven : Step1513Even) : Item1513R :=
  item1513R_of h131 h132 h133 hset h159 h1510 hBr h1511 h1411 hloc h153 hnorm hHJ hmeets htv
    (step1513NoTransv_of h131) hmax heven

end CFSG.RankThree.PartTwo.Sec15
