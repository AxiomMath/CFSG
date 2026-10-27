module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2BigD4
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2TwoAsm
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompAlt
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompOdd
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4D0
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4Classes
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4Comm
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.LieType.Chevalley.TrialityAllCharTorusCoordinates
public import CFSG.LocalAnalysis.EvenBN.Common.SL2Module
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.LocalAnalysis.AGLEmbedding.KFactsFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.L32A.C.SkPf
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.EvenBN.TrialityD4
open CFSG.ComponentClassification.RankTwoExceptional.D4

theorem eq_one_of_mem_center_sl2 {L : Type*} [Field L] [CharP L 2] {A : SL2 L}
    (hA : A ∈ Subgroup.center (SL2 L)) : A = 1 := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
  have h5 : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
  have hr1 : r = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h5)
  subst hr1
  ext i j
  rw [← hrA]
  simp


section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

theorem d4Mr_facts (hσ : σ ^ 3 = 1) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3) :
    IsSimpleGroup ↥(d4Mr K σ) ∧
      Nat.card ↥(d4Mr K σ) = (2 ^ f) ^ 3 * (((2 ^ f) ^ 3) ^ 2 - 1) ∧
      ∀ x ∈ Subgroup.center ↥(d4Mr K σ), x = 1 := by
  have hσ3 : ∀ c, σ (σ (σ c)) = c := fun c => by
    have := congrArg (fun τ : K ≃+* K => τ c) hσ
    simpa [pow_succ] using this
  set L := orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ with hLdef
  let e : ↥(d4Mr K σ) ≃* SL2 L :=
    (MulEquiv.subgroupCongr (orbitRankOneHom_range (t := TwistTag.D4) (K := K)
      (σ := σ.toRingHom) ⟨0, by decide⟩)).symm.trans
        (MonoidHom.ofInjective (orbitRankOneHom_injective_D4 hσ ⟨0, by decide⟩)).symm
  have hL : Nat.card L = (2 ^ f) ^ 3 := by
    rw [hLdef, orbitField_D4_zero_eq_top σ hσ3, ← hK]
    exact Nat.card_congr Subfield.topEquiv.toEquiv
  have h8 : 4 ≤ Nat.card L := by
    rw [hL]
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left (Nat.le_self_pow (by omega) 2) 3
  have := CFSG.LocalAnalysis.EvenBN.Common.sl2_isSimpleGroup_of_charTwo h8
  refine ⟨e.isSimpleGroup, ?_, fun x hx => ?_⟩
  · rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hL]
  · have hx' : e x ∈ Subgroup.center (SL2 L) :=
      Subgroup.mem_center_iff.mpr fun y => by
        rw [← e.apply_symm_apply y, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx]
    exact e.injective ((eq_one_of_mem_center_sl2 hx').trans (map_one e).symm)

omit [Finite K] [CharP K 2] in
theorem exists_mul_of_mem_d4Vr_sup_d4Mr {g : ModGL TwistTag.D4.tag K}
    (hg : g ∈ d4Vr K σ ⊔ d4Mr K σ) : ∃ v ∈ d4Vr K σ, ∃ s ∈ d4Mr K σ, g = v * s := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (orbitRankOneGroup_le_normalizer_d4 σ ⟨0, by decide⟩), Set.mem_mul] at hg
  obtain ⟨v, hv, s, hs, rfl⟩ := hg
  exact ⟨v, hv, s, hs, rfl⟩

omit [Finite K] [CharP K 2] in
theorem exists_pow_eq_mul_pow_d4 {v s : ModGL TwistTag.D4.tag K} (hv : v ∈ d4Vr K σ)
    (hs : s ∈ d4Mr K σ) (k : ℕ) : ∃ v' ∈ d4Vr K σ, (v * s) ^ k = v' * s ^ k := by
  induction k with
  | zero => exact ⟨1, one_mem _, by rw [pow_zero, pow_zero, mul_one]⟩
  | succ k ih =>
    obtain ⟨v', hv', hk⟩ := ih
    have hN := orbitRankOneGroup_le_normalizer_d4 σ ⟨0, by decide⟩ (pow_mem hs k)
    refine ⟨v' * (s ^ k * v * (s ^ k)⁻¹),
      mul_mem hv' ((Subgroup.mem_normalizer_iff.mp hN v).mp hv), ?_⟩
    rw [pow_succ, hk, pow_succ]
    group

theorem exists_pow_eq_one_of_mem_d4Vr {v : ModGL TwistTag.D4.tag K} (hv : v ∈ d4Vr K σ) :
    ∃ j : ℕ, v ^ 2 ^ j = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : IsPGroup 2 ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) :=
    (isPGroup_posUnipotent 2 TwistTag.D4.tag).to_le inf_le_left
  obtain ⟨j, hj⟩ := (hU.to_le (graphFixedSimpleComplement_le _)) ⟨v, hv⟩
  refine ⟨j, ?_⟩
  have h1 := congrArg Subtype.val hj
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1
  exact h1

theorem exists_pow_seven_of_normal_d4 (hσ : σ ^ 3 = 1) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (h7 : 7 ∣ (2 ^ f) ^ 3 - 1)
    {N : Subgroup (ModGL TwistTag.D4.tag K)}
    (hN : N ≤ d4C K σ ⊓ Subgroup.centralizer {d4z K})
    (hNn : ∀ g ∈ d4C K σ ⊓ Subgroup.centralizer {d4z K}, ∀ y ∈ N, g * y * g⁻¹ ∈ N)
    {x : ModGL TwistTag.D4.tag K} (hxN : x ∈ N) (hxV : x ∉ d4Vr K σ) :
    ∃ y ∈ N, y ≠ 1 ∧ y ^ 7 = 1 := by
  have hσ3 : ∀ c, σ (σ (σ c)) = c := fun c => by
    have := congrArg (fun τ : K ≃+* K => τ c) hσ
    simpa [pow_succ] using this
  have hC := centralizer_d4z_eq σ hσ3
  rw [hC] at hN hNn
  have hMN := orbitRankOneGroup_le_normalizer_d4 σ ⟨0, by decide⟩
  have hVM : d4Vr K σ ⊓ d4Mr K σ = ⊥ := complement_inf_orbitRankOneGroup_d4 σ ⟨0, by decide⟩
  obtain ⟨hsimple, hcard, -⟩ := d4Mr_facts σ hσ hf hK
  let N₁ : Subgroup ↥(d4Mr K σ) :=
    { carrier := {s | ∃ v ∈ d4Vr K σ, v * (s : ModGL TwistTag.D4.tag K) ∈ N}
      mul_mem' := by
        rintro s₁ s₂ ⟨v₁, hv₁, h₁⟩ ⟨v₂, hv₂, h₂⟩
        refine ⟨v₁ * ((s₁ : ModGL TwistTag.D4.tag K) * v₂ * (s₁ : ModGL TwistTag.D4.tag K)⁻¹),
          mul_mem hv₁ ((Subgroup.mem_normalizer_iff.mp (hMN s₁.2) v₂).mp hv₂), ?_⟩
        have := mul_mem h₁ h₂
        rw [Subgroup.coe_mul]
        convert this using 1
        group
      one_mem' := ⟨1, one_mem _, by rw [one_mul]; exact one_mem _⟩
      inv_mem' := by
        rintro s ⟨v, hv, h⟩
        refine ⟨(s : ModGL TwistTag.D4.tag K)⁻¹ * v⁻¹ * (s : ModGL TwistTag.D4.tag K), ?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp (hMN (inv_mem s.2)) v⁻¹).mp (inv_mem hv)
          rwa [inv_inv] at this
        · have := inv_mem h
          rw [Subgroup.coe_inv]
          convert this using 1
          group }
  have hN₁ : N₁.Normal := ⟨fun s ⟨v, hv, h⟩ m => by
    refine ⟨(m : ModGL TwistTag.D4.tag K) * v * (m : ModGL TwistTag.D4.tag K)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hMN m.2) v).mp hv, ?_⟩
    have := hNn m (Subgroup.mem_sup_right m.2) _ h
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    convert this using 1
    group⟩
  obtain ⟨v₀, hv₀, s₀, hs₀, rfl⟩ := exists_mul_of_mem_d4Vr_sup_d4Mr σ (hN hxN)
  have hs₀1 : s₀ ≠ 1 := by
    rintro rfl
    rw [mul_one] at hxV
    exact hxV hv₀
  have hs₀N : (⟨s₀, hs₀⟩ : ↥(d4Mr K σ)) ∈ N₁ := ⟨v₀, hv₀, hxN⟩
  have hN₁top : N₁ = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N₁ with h | h
    · rw [h, Subgroup.mem_bot] at hs₀N
      exact absurd (congrArg Subtype.val hs₀N) hs₀1
    · exact h
  have h7M : 7 ∣ Nat.card ↥(d4Mr K σ) := by
    rw [hcard]
    obtain ⟨c, hc⟩ := h7
    have hpos : 1 ≤ (2 ^ f) ^ 3 := Nat.one_le_pow _ _ (by positivity)
    have e1 : (2 ^ f) ^ 3 = 7 * c + 1 := by omega
    have e2 : ((2 ^ f) ^ 3) ^ 2 - 1 = 7 * (c * (7 * c + 2)) := by
      rw [e1]
      have : (7 * c + 1) ^ 2 = 7 * (c * (7 * c + 2)) + 1 := by ring
      omega
    rw [e2]
    exact Dvd.dvd.mul_left (Dvd.intro _ rfl) _
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  obtain ⟨m, hm⟩ := exists_prime_orderOf_dvd_card' 7 h7M
  have hmN : m ∈ N₁ := hN₁top ▸ Subgroup.mem_top m
  obtain ⟨v, hv, hn⟩ := hmN
  set n := v * (m : ModGL TwistTag.D4.tag K) with hndef
  have hm' : orderOf (m : ModGL TwistTag.D4.tag K) = 7 := by
    rw [Subgroup.orderOf_coe, hm]
  obtain ⟨v₇, hv₇, h7n⟩ := exists_pow_eq_mul_pow_d4 σ hv m.2 7
  have h7n' : n ^ 7 = v₇ := by
    rw [hndef, h7n, ← hm', pow_orderOf_eq_one, mul_one]
  obtain ⟨j, hj⟩ := exists_pow_eq_one_of_mem_d4Vr σ hv₇
  refine ⟨n ^ 2 ^ j, pow_mem hn _, fun h1 => ?_, ?_⟩
  · obtain ⟨v', hv', h2⟩ := exists_pow_eq_mul_pow_d4 σ hv m.2 (2 ^ j)
    have h2' : v' * (m : ModGL TwistTag.D4.tag K) ^ 2 ^ j = 1 := by
      rw [← h2]
      exact h1
    have h3 : (m : ModGL TwistTag.D4.tag K) ^ 2 ^ j ∈ d4Vr K σ ⊓ d4Mr K σ := by
      refine Subgroup.mem_inf.mpr ⟨?_, pow_mem m.2 _⟩
      rw [eq_inv_of_mul_eq_one_right h2']
      exact inv_mem hv'
    rw [hVM, Subgroup.mem_bot] at h3
    have h4 := orderOf_dvd_of_pow_eq_one h3
    rw [hm'] at h4
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
      ((show Nat.Prime 7 by norm_num).dvd_of_dvd_pow h4)
    omega
  · rw [← pow_mul, mul_comm, pow_mul, h7n', hj]

theorem le_d4Vr_of_normal (hσ : σ ^ 3 = 1) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (h7 : 7 ∣ (2 ^ f) ^ 3 - 1)
    {N : Subgroup (ModGL TwistTag.D4.tag K)}
    (hN : N ≤ d4C K σ ⊓ Subgroup.centralizer {d4z K})
    (hNn : ∀ g ∈ d4C K σ ⊓ Subgroup.centralizer {d4z K}, ∀ y ∈ N, g * y * g⁻¹ ∈ N)
    (h3 : ∀ y ∈ N, Odd (orderOf y) → y ^ 3 = 1) : N ≤ d4Vr K σ := by
  intro x hx
  by_contra hxV
  obtain ⟨y, hyN, hy1, hy7⟩ := exists_pow_seven_of_normal_d4 σ hσ hf hK h7 hN hNn hx hxV
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hord : orderOf y = 7 := orderOf_eq_prime hy7 hy1
  have h73 := orderOf_dvd_of_pow_eq_one (h3 y hyN (by rw [hord]; decide))
  rw [hord] at h73
  norm_num at h73

theorem exists_E9_3d4 (hσ : σ ^ 3 = 1) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hk : Nat.card (trialityFixedField K σ.toRingHom) = 2 ^ f) :
    ∃ E : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨-, hcardM, hZM⟩ := d4Mr_facts σ hσ hf hK
  have hL1 : orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ =
      trialityFixedField K σ.toRingHom := by
    ext c
    rw [mem_orbitField_D4_one]
    exact Iff.rfl
  have hcardD : Nat.card ↥(d4D0z K σ) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    rw [Nat.card_congr (d4D0zEquiv σ hσ).toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hL1, hk]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3pow : ∀ n : ℕ, 3 ∣ 4 ^ n - 1 := fun n => by
    simpa using Nat.sub_dvd_pow_sub_pow (x := 4) (y := 1) (n := n)
  have h3M : 3 ∣ Nat.card ↥(d4Mr K σ) := by
    rw [hcardM, show ((2 ^ f) ^ 3) ^ 2 = 4 ^ (3 * f) by
      rw [← pow_mul, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf]
    exact Dvd.dvd.mul_left (h3pow _) _
  have h3D : 3 ∣ Nat.card ↥(d4D0z K σ) := by
    rw [hcardD, show (2 ^ f) ^ 2 = 4 ^ f by
      rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm]]
    exact Dvd.dvd.mul_left (h3pow _) _
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3 h3M
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 3 h3D
  set C₀ := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  have hMC : d4Mr K σ ≤ C₀ := d4Mr_le σ hσ
  have hDC : d4D0z K σ ≤ C₀ := d4D0z_le σ
  let a₀ : ↥C₀ := ⟨a, hMC a.2⟩
  let b₀ : ↥C₀ := ⟨b, hDC b.2⟩
  have ha₀ : orderOf a₀ = 3 := by
    rw [← Subgroup.orderOf_coe a₀, show ((a₀ : ↥C₀) : ModGL TwistTag.D4.tag K) = a from rfl,
      Subgroup.orderOf_coe, ha]
  have hb₀ : orderOf b₀ = 3 := by
    rw [← Subgroup.orderOf_coe b₀, show ((b₀ : ↥C₀) : ModGL TwistTag.D4.tag K) = b from rfl,
      Subgroup.orderOf_coe, hb]
  have hxM : ∀ x ∈ Subgroup.zpowers a₀, ((x : ↥C₀) : ModGL TwistTag.D4.tag K) ∈ d4Mr K σ := by
    rintro _ ⟨n, rfl⟩
    exact zpow_mem a.2 n
  have hyD : ∀ y ∈ Subgroup.zpowers b₀, ((y : ↥C₀) : ModGL TwistTag.D4.tag K) ∈ d4D0z K σ := by
    rintro _ ⟨n, rfl⟩
    exact zpow_mem b.2 n
  have hcomm : ∀ x : ↥(Subgroup.zpowers a₀), ∀ y : ↥(Subgroup.zpowers b₀),
      Commute ((Subgroup.zpowers a₀).subtype x) ((Subgroup.zpowers b₀).subtype y) := by
    intro x y
    apply Subtype.ext
    exact (d4D0z_commute_d4Mr σ _ (hyD _ y.2) _ (hxM _ x.2)).symm
  let φ := MonoidHom.noncommCoprod (Subgroup.zpowers a₀).subtype (Subgroup.zpowers b₀).subtype
    hcomm
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ hxy
    change (x : ↥C₀) * (y : ↥C₀) = 1 at hxy
    have hxy' : (x : ↥C₀) = (y : ↥C₀)⁻¹ := eq_inv_of_mul_eq_one_left hxy
    have hxD : ((x : ↥C₀) : ModGL TwistTag.D4.tag K) ∈ d4D0z K σ := by
      rw [hxy', Subgroup.coe_inv]
      exact inv_mem (hyD _ y.2)
    have hx1 : (x : ↥C₀) = 1 := by
      have hz := hZM ⟨_, hxM _ x.2⟩ (Subgroup.mem_center_iff.mpr fun m => Subtype.ext
        (d4D0z_commute_d4Mr σ _ hxD _ m.2).symm)
      have h' : ((x : ↥C₀) : ModGL TwistTag.D4.tag K) = 1 := congrArg Subtype.val hz
      exact Subtype.ext h'
    have hy1 : (y : ↥C₀) = 1 := by
      rw [hx1] at hxy'
      exact inv_eq_one.mp hxy'.symm
    exact Prod.ext (Subtype.ext hx1) (Subtype.ext hy1)
  have h3a : a₀ ^ 3 = 1 := by rw [← ha₀]; exact pow_orderOf_eq_one a₀
  have h3b : b₀ ^ 3 = 1 := by rw [← hb₀]; exact pow_orderOf_eq_one b₀
  have hca : ∀ x x' : ↥(Subgroup.zpowers a₀), x * x' = x' * x := by
    rintro ⟨_, n, rfl⟩ ⟨_, m, rfl⟩
    exact Subtype.ext (Commute.zpow_zpow_self a₀ n m).eq
  have hcb : ∀ y y' : ↥(Subgroup.zpowers b₀), y * y' = y' * y := by
    rintro ⟨_, n, rfl⟩ ⟨_, m, rfl⟩
    exact Subtype.ext (Commute.zpow_zpow_self b₀ n m).eq
  have hxa : ∀ x : ↥(Subgroup.zpowers a₀), x ^ 3 = 1 := by
    rintro ⟨_, n, rfl⟩
    apply Subtype.ext
    change (a₀ ^ n) ^ 3 = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h3a, one_zpow]
  have hyb : ∀ y : ↥(Subgroup.zpowers b₀), y ^ 3 = 1 := by
    rintro ⟨_, n, rfl⟩
    apply Subtype.ext
    change (b₀ ^ n) ^ 3 = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h3b, one_zpow]
  refine ⟨φ.range, ⟨⟨⟨fun u w => ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨p, hu⟩ := u.2
    obtain ⟨p', hw⟩ := w.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hu, ← hw, ← map_mul, ← map_mul]
    exact congrArg φ (Prod.ext (hca _ _) (hcb _ _))
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    rw [← map_pow]
    have h1 : ((x, y) : ↥(Subgroup.zpowers a₀) × ↥(Subgroup.zpowers b₀)) ^ 3 = 1 :=
      Prod.ext (by rw [Prod.pow_fst, hxa]; rfl) (by rw [Prod.pow_snd, hyb]; rfl)
    rw [h1, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, Nat.card_prod, Nat.card_zpowers,
      Nat.card_zpowers, ha₀, hb₀]

end Model

theorem false_of_autConf_3d4_small {M : Type} [Group M] {f : ℕ} (hf1 : 1 ≤ f) (hf2 : f ≤ 2)
    (hM : ChevalleyExceptionalModel M .trialityD4 2 f) {ν : MulAut M}
    {Lb Pb : Subgroup (MulAut M)} (h : AutConf M ν Lb Pb) (hP : Nat.card Pb = 9) : False := by
  have hcard : Nat.card M = CFSG.Open.ordTrialityD4 (2 ^ f) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hM
  obtain ⟨K, _, _, _, σ, hσ3, hσq, hK, hk, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.TrialityCover.triality_model hf1 hM.2
  have hσ : σ.toRingHom ^ 3 = 1 := RingHom.ext fun c => ringEquiv_cube_apply_eq hK hσq c
  have hσ' : ∀ c, σ (σ (σ c)) = c := fun c => ringEquiv_cube_apply_eq hK hσq c
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  set C₀ := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC₀
  have hZ : Subgroup.center ↥C₀ = ⊥ := exceptional_fixed_center_trivial TwistTag.D4 K σ
  have hcj := conj_injective_of_center_eq_bot hZ
  have h₀ := h.map e
  obtain ⟨S, hS, hSν⟩ := h₀.sylow
  obtain ⟨g, hg⟩ := exists_map_conj_eq hS (isSylowTwoOf_d4U (σ := σ))
  have h₁ := h₀.map (MulAut.conj g)
  set ν₁ := MulAut.congr (MulAut.conj g) (MulAut.congr e ν) with hν₁def
  set Lb₁ := (Lb.map (MulAut.congr e).toMonoidHom).map
    (MulAut.congr (MulAut.conj g)).toMonoidHom with hLb₁
  set Pb₁ := (Pb.map (MulAut.congr e).toMonoidHom).map
    (MulAut.congr (MulAut.conj g)).toMonoidHom with hPb₁
  have hP₁ : Nat.card Pb₁ = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.congr _).injective,
      Subgroup.card_map_of_injective (MulAut.congr _).injective, hP]
  have hfix : ∀ u ∈ (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf C₀,
      ν₁ u = u := by
    intro u hu
    rw [← hg] at hu
    obtain ⟨s, hs, rfl⟩ := hu
    change MulAut.conj g (MulAut.congr e ν ((MulAut.conj g).symm (MulAut.conj g s))) =
      MulAut.conj g s
    rw [MulEquiv.symm_apply_apply, hSν s hs]
  have h34 : ¬ IsPSL 3 2 2 ↥C₀ := fun h34 => by
    have h1 := card_of_isPSL34 h34
    rw [← Nat.card_congr e.toEquiv, hcard] at h1
    revert h1
    interval_cases f <;> (unfold CFSG.Open.ordTrialityD4; norm_num)
  have hSd : (modelData hf1 K σ hσ hσq hK hk).S =
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf C₀ := Model.sixClosure_eq σ hσ
  have hCB := cbAt_trialityD4Data (modelData hf1 K σ hσ hσq hK hk)
  rw [hSd] at hCB
  obtain ⟨z, hzU, hzc, hν₁⟩ := exists_eq_conj_of_fix (n4At_d4 (σ := σ) hf1 hK hσq) h34 hCB
    ⟨1, by rw [pow_one]; exact h₁.sq⟩ hfix
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact h₁.ne_one (by rw [hν₁, map_one])
  have hzV : z ∈ (modelData hf1 K σ hσ hσq hK hk).V := by
    rw [← (modelData hf1 K σ hσ hσq hK hk).S_inf_centralizer_S, hSd]
    exact ⟨hzU, Subgroup.mem_centralizer_iff.mpr fun y hy => (hzc y hy).symm⟩
  obtain ⟨c, hc⟩ := hzV
  change fixedSubfield σ at c
  have hzc6 : z = Model.cx₆ σ hσ c := hc.symm
  have hc0 : (c : K) ≠ 0 := by
    intro h0
    apply hz1
    rw [hzc6]
    apply Subtype.ext
    change pinnedX TwistTag.D4.tag K (trialityRoot 5) (c : K) = 1
    rw [h0]
    exact pinnedX_zero _ _ _
  let β : (trialityFixedField K σ.toRingHom)ˣ :=
    Units.mk0 ⟨(c : K), c.2⟩ fun h0 => hc0 (congrArg Subtype.val h0)
  set g₀ := trialityMiddleTorus K σ β with hg₀def
  have hg₀ : g₀ ∈ d4C K σ := trialityMiddleTorus_mem_d4C σ hσ' β
  have hg₀z : g₀ * d4z K * g₀⁻¹ = (z : ModGL TwistTag.D4.tag K) := by
    rw [d4z, hm_conj_d4x₆ σ β 1, mul_one, hzc6]
    rfl
  set H₀ := Lb₁.comap (MulAut.conj : ↥C₀ →* MulAut ↥C₀) with hH₀
  set H := (H₀.map C₀.subtype).map (MulAut.conj g₀⁻¹).toMonoidHom with hHdef
  have hwz : ∀ w ∈ H₀, w * z = z * w := fun w hw => hcj (by
    rw [map_mul, map_mul, ← hν₁]
    exact h₁.comm _ hw)
  have hHC : H ≤ d4C K σ ⊓ Subgroup.centralizer {d4z K} := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    · change g₀⁻¹ * (w : ModGL TwistTag.D4.tag K) * g₀⁻¹⁻¹ ∈ d4C K σ
      exact mul_mem (mul_mem (inv_mem hg₀) w.2) (inv_mem (inv_mem hg₀))
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      change d4z K * (g₀⁻¹ * (w : ModGL TwistTag.D4.tag K) * g₀⁻¹⁻¹) =
        g₀⁻¹ * (w : ModGL TwistTag.D4.tag K) * g₀⁻¹⁻¹ * d4z K
      have h1 : (w : ModGL TwistTag.D4.tag K) * z = z * w := congrArg Subtype.val (hwz w hw)
      rw [← hg₀z] at h1
      calc d4z K * (g₀⁻¹ * (w : ModGL TwistTag.D4.tag K) * g₀⁻¹⁻¹) =
          g₀⁻¹ * ((g₀ * d4z K * g₀⁻¹) * w) * g₀ := by group
        _ = g₀⁻¹ * (w * (g₀ * d4z K * g₀⁻¹)) * g₀ := by rw [h1]
        _ = g₀⁻¹ * (w : ModGL TwistTag.D4.tag K) * g₀⁻¹⁻¹ * d4z K := by group
  have hHn : ∀ c' ∈ d4C K σ ⊓ Subgroup.centralizer {d4z K}, ∀ x ∈ H, c' * x * c'⁻¹ ∈ H := by
    rintro c' hc' _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    obtain ⟨hc'C, hc'z⟩ := Subgroup.mem_inf.mp hc'
    have hc'z' : d4z K * c' = c' * d4z K :=
      Subgroup.mem_centralizer_iff.mp hc'z (d4z K) (Set.mem_singleton _)
    let c'' : ↥C₀ := ⟨g₀ * c' * g₀⁻¹, mul_mem (mul_mem hg₀ hc'C) (inv_mem hg₀)⟩
    have hc''z : ν₁ c'' = c'' := by
      rw [hν₁, MulAut.conj_apply]
      apply Subtype.ext
      change (z : ModGL TwistTag.D4.tag K) * (g₀ * c' * g₀⁻¹) * (z : ModGL TwistTag.D4.tag K)⁻¹ =
        g₀ * c' * g₀⁻¹
      rw [← hg₀z]
      calc g₀ * d4z K * g₀⁻¹ * (g₀ * c' * g₀⁻¹) * (g₀ * d4z K * g₀⁻¹)⁻¹ =
          g₀ * (d4z K * c') * (d4z K)⁻¹ * g₀⁻¹ := by group
        _ = g₀ * (c' * d4z K) * (d4z K)⁻¹ * g₀⁻¹ := by rw [hc'z']
        _ = g₀ * c' * g₀⁻¹ := by group
    have h2 := h₁.norm c'' hc''z _ hw
    have hmem : c'' * w * c''⁻¹ ∈ H₀ := by
      change MulAut.conj (c'' * w * c''⁻¹) ∈ Lb₁
      rwa [map_mul, map_mul, map_inv]
    refine ⟨_, ⟨_, hmem, rfl⟩, ?_⟩
    change g₀⁻¹ * ((c'' * w * c''⁻¹ : ↥C₀) : ModGL TwistTag.D4.tag K) * g₀⁻¹⁻¹ =
      c' * (g₀⁻¹ * (w : ModGL TwistTag.D4.tag K) * g₀⁻¹⁻¹) * c'⁻¹
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    change g₀⁻¹ * ((g₀ * c' * g₀⁻¹) * (w : ModGL TwistTag.D4.tag K) * (g₀ * c' * g₀⁻¹)⁻¹) *
      g₀⁻¹⁻¹ = c' * (g₀⁻¹ * (w : ModGL TwistTag.D4.tag K) * g₀⁻¹⁻¹) * c'⁻¹
    group
  have hH3 : ∀ x ∈ H, Odd (orderOf x) → x ^ 3 = 1 := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩ hodd
    have ho : orderOf ((MulAut.conj g₀⁻¹).toMonoidHom (C₀.subtype w)) =
        orderOf (MulAut.conj w) := by
      rw [orderOf_injective _ (MulAut.conj g₀⁻¹).injective,
        orderOf_injective _ C₀.subtype_injective, orderOf_injective _ hcj]
    rw [ho] at hodd
    have hw3 : w ^ 3 = 1 := hcj (by rw [map_pow, map_one]; exact h₁.three _ hw hodd)
    rw [← map_pow, ← map_pow, hw3, map_one, map_one]
  have h7 : 7 ∣ (2 ^ f) ^ 3 - 1 := by
    rw [← pow_mul, mul_comm, pow_mul, show (2 : ℕ) ^ 3 = 8 by norm_num]
    simpa using Nat.sub_dvd_pow_sub_pow (x := 8) (y := 1) (n := f)
  have hHV := le_d4Vr_of_normal σ hσ3 hf1 hK h7 hHC hHn hH3
  obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, -, hcardAut, -⟩ :=
    even_triality_exact_automorphism_normal_form hf1 K hK σ hσq
  have hinj : Function.Injective fun p : ↥Pb₁ => Θ p := by
    intro p p' hpp
    have hpp' : Θ p = Θ p' := hpp
    have hq : (p : MulAut ↥C₀)⁻¹ * p' ∈ Θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hpp', inv_mul_cancel]
    rw [hker] at hq
    obtain ⟨w, hw⟩ := hq
    have hqP : (p : MulAut ↥C₀)⁻¹ * p' ∈ Pb₁ := mul_mem (inv_mem p.2) p'.2
    have hwH₀ : w ∈ H₀ := by
      change MulAut.conj w ∈ Lb₁
      rw [hw]
      exact h₁.le hqP
    have hw3 : w ^ 3 = 1 := hcj (by rw [map_pow, hw, map_one]; exact h₁.elem.2 _ hqP)
    have hwV : (MulAut.conj g₀⁻¹).toMonoidHom (C₀.subtype w) ∈ d4Vr K σ :=
      hHV ⟨_, ⟨w, hwH₀, rfl⟩, rfl⟩
    obtain ⟨j, hj⟩ := exists_pow_eq_one_of_mem_d4Vr σ hwV
    have h3' : ((MulAut.conj g₀⁻¹).toMonoidHom (C₀.subtype w)) ^ 3 = 1 := by
      rw [← map_pow, ← map_pow, hw3, map_one, map_one]
    have h1 : orderOf ((MulAut.conj g₀⁻¹).toMonoidHom (C₀.subtype w)) ∣ Nat.gcd 3 (2 ^ j) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3') (orderOf_dvd_of_pow_eq_one hj)
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right _ (by norm_num)), Nat.dvd_one,
      orderOf_eq_one_iff] at h1
    have hw1 : w = 1 := Subtype.ext ((MulAut.conj g₀⁻¹).injective (h1.trans (map_one _).symm))
    rw [hw1, map_one] at hw
    exact Subtype.ext (inv_mul_eq_one.mp hw.symm)
  have : Finite (K ≃+* K) := Finite.of_injective (fun τ : K ≃+* K => (τ : K → K))
    fun a b hab => RingEquiv.ext (congrFun hab)
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [hP₁, hcardAut] at hle
  omega

theorem not_3d4_small {Q : Type} [Group Q] {K L P T : Subgroup Q} {v : Q}
    (hQ : Vol2Native.SQTKHypCat Q) (h : Conf12626 K L P T v) {f : ℕ} (hf1 : 1 ≤ f)
    (hf2 : f ≤ 2) : ¬ ChevalleyExceptionalModel ↥K .trialityD4 2 f := fun hM => by
  have := hQ.finite
  obtain ⟨F, _, _, _, σ, hσ3, hσq, hF, hk, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.TrialityCover.triality_model hf1 hM.2
  obtain ⟨E, hE, hE9⟩ := exists_E9_3d4 σ hσ3 hf1 hF hk
  have h9 := h.card_map_rhoP_eq_nine hQ e
    (fun z hz => by rwa [exceptional_fixed_center_trivial, Subgroup.mem_bot] at hz) hE hE9
  rw [Subgroup.card_map_of_injective (MulAut.congr e).injective] at h9
  exact false_of_autConf_3d4_small hf1 hf2 hM h.autConf h9

theorem comp12626D42_holds : Comp12626D42 :=
  fun _ _ _ _ _ _ _ hQ h => not_3d4_small hQ h le_rfl (by norm_num)

theorem not_3d44 {Q : Type} [Group Q] {K L P T : Subgroup Q} {v : Q}
    (hQ : Vol2Native.SQTKHypCat Q) (h : Conf12626 K L P T v) :
    ¬ ChevalleyExceptionalModel ↥K .trialityD4 2 2 :=
  not_3d4_small hQ h (by norm_num) le_rfl

end CFSG.Quasithin.H13.S126C
