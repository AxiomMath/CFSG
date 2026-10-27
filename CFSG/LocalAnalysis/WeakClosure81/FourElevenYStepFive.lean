module

public import CFSG.LocalAnalysis.WeakClosure81.FourElevenBasic
public import CFSG.LocalAnalysis.WeakClosure81.FourElevenLevi
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupNormalQuasisimple
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5FusionTwoAction
public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.WeakClosure81.FourEleven

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped MatrixGroups commutatorElement

variable {Q : Type} [Group Q] [Finite Q]

section Sl2Five

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

theorem sl2_five_quasisimple : CFSG.Open.IsQuasisimple (SL(2, ZMod 5)) := by
  have h4 : 4 ≤ Nat.card (ZMod 5) := by
    rw [Nat.card_zmod]
    norm_num
  exact ⟨(CFSG.ClassicalInvolution.sl2_isPerfect (F := ZMod 5) h4).commutator_eq_top,
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := ZMod 5) h4⟩

end Sl2Five

omit [Finite Q] in
theorem LeviData.isQuasisimple_five {L : Subgroup Q} {z : Q} {Y : Subgroup Q}
    (hY : LeviData L 5 z Y) : CFSG.Open.IsQuasisimple ↥Y := by
  obtain ⟨e⟩ := hY.sl2
  exact sl2_five_quasisimple.of_mulEquiv e

omit [Finite Q] in
theorem LeviData.exists_pow_mem_five {L : Subgroup Q} [L.Normal]
    (hL : LieModel ↥L .PSL 3 5 1 ∨ LieModel ↥L .PSU 3 5 1) (h2 : IsPGroup 2 (Q ⧸ L))
    {Y : Subgroup Q} {z : Q} (hY : LeviData L 5 z Y) :
    ∀ x ∈ centralizer ({z} : Set Q), ∃ k : ℕ, x ^ 2 ^ k ∈ Y := by
  intro x hx
  have hfive := LeviData.five hL hY
  obtain ⟨k, hk⟩ : ∃ k : ℕ, x ^ 2 ^ k ∈ L := by
    obtain ⟨k, hk⟩ := (isPGroup_iff_pow_pow_eq_one.mp h2) (QuotientGroup.mk' L x)
    refine ⟨k, (QuotientGroup.eq_one_iff (x ^ 2 ^ k)).mp ?_⟩
    have hk' : (QuotientGroup.mk' L) (x ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact hk
    simpa using hk'
  have hxK : x ^ 2 ^ k ∈ centralizer ({z} : Set Q) :=
    (Subgroup.centralizer ({z} : Set Q)).pow_mem hx _
  have hu : x ^ 2 ^ k ∈ L ⊓ centralizer ({z} : Set Q) :=
    Subgroup.mem_inf.mpr ⟨hk, hxK⟩
  obtain ⟨m, hm⟩ := hfive.2 (x ^ 2 ^ k) hu
  refine ⟨k + m, ?_⟩
  rw [pow_add, pow_mul]
  exact hm

omit [Finite Q] in
theorem isPGroup_inf_centralizer_five {L : Subgroup Q} [L.Normal]
    (hL : LieModel ↥L .PSL 3 5 1 ∨ LieModel ↥L .PSU 3 5 1) (h2 : IsPGroup 2 (Q ⧸ L))
    {Y : Subgroup Q} {z : Q} (hY : LeviData L 5 z Y) :
    IsPGroup 2 ↥(centralizer ({z} : Set Q) ⊓ centralizer (Y : Set Q)) := by
  have hfive := LeviData.five hL hY
  rw [isPGroup_iff_pow_pow_eq_one]
  rintro ⟨x, hx⟩
  obtain ⟨hxK, hxC⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨k, hk⟩ : ∃ k : ℕ, x ^ 2 ^ k ∈ L := by
    obtain ⟨k, hk⟩ := (isPGroup_iff_pow_pow_eq_one.mp h2) (QuotientGroup.mk' L x)
    refine ⟨k, (QuotientGroup.eq_one_iff (x ^ 2 ^ k)).mp ?_⟩
    have hk' : (QuotientGroup.mk' L) (x ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact hk
    simpa using hk'
  have hu : x ^ 2 ^ k ∈ L ⊓ centralizer (Y : Set Q) :=
    Subgroup.mem_inf.mpr ⟨hk, (Subgroup.centralizer (Y : Set Q)).pow_mem hxC _⟩
  obtain ⟨m, hm⟩ := hfive.1.exists_pow_pow_eq_one ⟨x ^ 2 ^ k, hu⟩
  refine ⟨k + m, ?_⟩
  apply Subtype.ext
  show x ^ 2 ^ (k + m) = 1
  rw [pow_add, pow_mul]
  simpa using congrArg Subtype.val hm

theorem LeviData.inCalEi_two_centralizer_five {L : Subgroup Q} [L.Normal]
    (hL : LieModel ↥L .PSL 3 5 1 ∨ LieModel ↥L .PSU 3 5 1)
    (hO2 : pCoreOf 2 (⊤ : Subgroup Q) = ⊥) (h2 : IsPGroup 2 (Q ⧸ L)) {T A Y : Subgroup Q}
    {z : Q} (hT : IsSylowIn 2 T ⊤) (hAT : A ≤ T) (hA : IsElemAbelian 2 A)
    (hcard : Nat.card A = 8) (hzA : z ∈ A) (hz2 : orderOf z = 2)
    (hzT : T ≤ centralizer ({z} : Set Q))
    (hY : LeviData L 5 z Y) (hAY : ¬ A ≤ centralizer (Y : Set Q)) :
    UniquenessCase.PartTwo.InCalEi 2 T A (centralizer ({z} : Set Q)) := by
  let K : Subgroup Q := centralizer ({z} : Set Q)
  have hTK : T ≤ K := hzT
  have hAK : A ≤ K := hAT.trans hTK
  have hYK : Y ≤ K := by
    rw [hY.eq_commutator]
    exact (Subgroup.commutator_le_self _).trans inf_le_right
  have hYn : (Y.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYK).mpr hY.centralizer_le_normalizer
  have hYq : CFSG.Open.IsQuasisimple ↥Y := hY.isQuasisimple_five
  have hYkq : CFSG.Open.IsQuasisimple ↥(Y.subgroupOf K) :=
    hYq.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hYK)
  have hRkn : (CFSG.solvableRadical ↥K).Normal := inferInstance
  have hRks : Group.IsSolvable ↥(CFSG.solvableRadical ↥K) :=
    CFSG.Quasithin.A3.solvableRadical_isSolvable
  have hR_le_k : CFSG.solvableRadical ↥K ≤
      Subgroup.centralizer (Y.subgroupOf K : Set ↥K) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (@CFSG.ComponentClassification.AschbacherTheorem5.FusionTwo.commute_of_quasisimple
      ↥K _ (Y.subgroupOf K) (CFSG.solvableRadical ↥K) hYkq hYn hRkn hRks r hr y hy).symm
  have hR_le : (CFSG.solvableRadical ↥K).map K.subtype ≤ centralizer (Y : Set Q) := by
    rintro x ⟨r, hr, rfl⟩
    have hc := hR_le_k hr
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    have hyK : y ∈ K := hYK hy
    have hyYk : (⟨y, hyK⟩ : ↥K) ∈ Y.subgroupOf K := Subgroup.mem_subgroupOf.mpr hy
    simpa using congrArg Subtype.val (hc ⟨y, hyK⟩ hyYk)
  have hOle : pCoreOf 2 K ≤ K := pCoreOf_le 2 K
  have hOn : ((pCoreOf 2 K).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOle).mpr (le_normalizer_pCoreOf 2 K)
  have hOs : Group.IsSolvable ↥((pCoreOf 2 K).subgroupOf K) := by
    have hp : IsPGroup 2 ↥((pCoreOf 2 K).subgroupOf K) :=
      (pCoreOf_isPGroup 2 K).comap_subtype
    exact @IsNilpotent.to_isSolvable ↥((pCoreOf 2 K).subgroupOf K) _ hp.isNilpotent
  have hO_le_k : (pCoreOf 2 K).subgroupOf K ≤
      Subgroup.centralizer (Y.subgroupOf K : Set ↥K) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (@CFSG.ComponentClassification.AschbacherTheorem5.FusionTwo.commute_of_quasisimple
      ↥K _ (Y.subgroupOf K) ((pCoreOf 2 K).subgroupOf K) hYkq hYn hOn hOs r hr y hy).symm
  have hOmap : ((pCoreOf 2 K).subgroupOf K).map K.subtype = pCoreOf 2 K := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hOle]
  have hO_le : pCoreOf 2 K ≤ centralizer (Y : Set Q) := by
    rw [← hOmap]
    rintro x ⟨r, hr, rfl⟩
    have hc := hO_le_k hr
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    have hyK : y ∈ K := hYK hy
    have hyYk : (⟨y, hyK⟩ : ↥K) ∈ Y.subgroupOf K := Subgroup.mem_subgroupOf.mpr hy
    simpa using congrArg Subtype.val (hc ⟨y, hyK⟩ hyYk)
  have hA_notO : ¬ A ≤ pCoreOf 2 K := fun hAO => hAY (hAO.trans hO_le)
  have hK2 : ∀ x ∈ K, ∃ k : ℕ, x ^ 2 ^ k ∈ Y := hY.exists_pow_mem_five hL h2
  have hCq2 : IsPGroup 2 ↥(K ⊓ centralizer (Y : Set Q)) :=
    isPGroup_inf_centralizer_five hL h2 hY
  have hR2 : IsPGroup 2 ↥(CFSG.solvableRadical ↥K) := by
    have hRleCq : (CFSG.solvableRadical ↥K).map K.subtype ≤
        K ⊓ centralizer (Y : Set Q) :=
      le_inf (Subgroup.map_subtype_le _) hR_le
    have hmap2 : IsPGroup 2 ↥((CFSG.solvableRadical ↥K).map K.subtype) :=
      hCq2.of_injective (Subgroup.inclusion hRleCq) (Subgroup.inclusion_injective hRleCq)
    exact hmap2.of_equiv
      (Subgroup.equivMapOfInjective (CFSG.solvableRadical ↥K) K.subtype
        K.subtype_injective).symm
  have hRtwo : CFSG.Quasithin.E1.IsTwoClosed (CFSG.solvableRadical ↥K) := by
    refine ⟨CFSG.solvableRadical ↥K, ⟨le_rfl, hR2, ?_⟩, ?_⟩
    · rw [Subgroup.relIndex_self]
      exact Nat.prime_two.not_dvd_one
    · rw [Subgroup.subgroupOf_self]
      infer_instance
  have hAJ : ∃ a ∈ A, ∃ x ∈ Y, ⁅a, x⁆ ∉ (CFSG.solvableRadical ↥K).map K.subtype := by
    by_contra h
    push Not at h
    have hle : ⁅A, Y⁆ ≤ (CFSG.solvableRadical ↥K).map K.subtype :=
      Subgroup.commutator_le.mpr h
    have hYperf : Group.IsPerfect ↥Y := ⟨hYq.1⟩
    have hbot : ⁅⁅Y, A⁆, Y⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hle.trans hR_le
    have hYA : ⁅Y, A⁆ = ⊥ := CFSG.LocalCores.perfect_double_commutator hYperf hbot
    apply hAY
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hYA
  have hEII : ECaseII T A K :=
    eCaseII_of_normal_quasisimple hYK hYn hYq hK2 hRtwo hAK hAJ
  have hTsylTop : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨hT.le, hT.isPGroup, hT.not_dvd_relIndex⟩
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ K) K := by
    rw [inf_eq_left.mpr hTK]
    exact hTsylTop.of_le hTK le_top
  have hzK : z ∈ K := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hzpowK : Subgroup.zpowers z ≤ K := Subgroup.zpowers_le.mpr hzK
  have hzpow2 : IsPGroup 2 (Subgroup.zpowers z) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hz2]
    norm_num
  have hKcent : K ≤ Subgroup.centralizer (Subgroup.zpowers z : Set Q) := by
    rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp hk
  have hzO : z ∈ pCoreOf 2 K :=
    le_pCoreOf_of_le_normalizer 2 hzpowK
      (hKcent.trans (Subgroup.centralizer_le_normalizer _)) hzpow2 (Subgroup.mem_zpowers z)
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have htA : tA T A ≤ T ⊓ K := by
    rw [tA_eq_inf_centralizer hO2 T A]
    exact le_inf inf_le_left (inf_le_left.trans hTK)
  refine ⟨⟨htA, hSyl, hA_notO, Or.inr hEII⟩, ?_⟩
  exact mQuot_le_of_card_le (n := 2) hA (by rw [hcard]; norm_num) hzA hzO hz1

end CFSG.LocalAnalysis.WeakClosure81.FourEleven
