module

public import CFSG.RankThree.PartTwo.Sec16.Item163StepsQProofDefs
public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs
public import CFSG.RankThree.PartTwo.Sec13.Item135Simple
public import CFSG.RankThree.PartTwo.Sec13.Item138N
import CFSG.RankThree.PartTwo.Sec16.Item169StepsProof1612
import CFSG.RankThree.PartTwo.Sec16.Item16TailMore
import CFSG.RankThree.PartTwo.Sec15.NoModNine
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.RankThree.PartTwo.Sec13.Item13Theta

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

namespace Proof163Shape

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_pow_two_of_mem_sup {L A : Subgroup G}
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hA3 : IsPGroup 3 A) {x : G}
    (hx : x ∈ L ⊔ A) {k : ℕ} (hxk : x ^ 2 ^ k = 1) : x ∈ L := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left L A hAL] at hx
  obtain ⟨l, hl, a, ha, rfl⟩ := hx
  have key : ∀ m : ℕ, (l * a) ^ m * (a ^ m)⁻¹ ∈ L := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have e : (l * a) ^ (m + 1) * (a ^ (m + 1))⁻¹ =
          ((l * a) ^ m * (a ^ m)⁻¹) * (a ^ m * l * (a ^ m)⁻¹) := by
        rw [pow_succ, pow_succ]
        group
      rw [e]
      exact mul_mem ih ((Subgroup.mem_normalizer_iff.mp (hAL (pow_mem ha m)) l).mp hl)
  have haL : a ^ 2 ^ k ∈ L := by
    have h1 := key (2 ^ k)
    rw [hxk, one_mul] at h1
    exact inv_mem_iff.mp h1
  obtain ⟨j, hj⟩ := hA3 ⟨a, ha⟩
  have haj : a ^ 3 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hcop : Nat.Coprime (2 ^ k) (orderOf a) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one haj)
      (Nat.Coprime.pow k j (by norm_num))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have haL' : a ∈ L := by
    rw [← hm]
    exact pow_mem haL m
  exact mul_mem hl haL'

theorem sup_inf_pCoreOf_eq_bot {A L Y : Subgroup G} (hA3 : IsPGroup 3 A)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hLY : L ≤ Y)
    (hO : CFSG.Open.pCoreOf 2 L = ⊥) : (A ⊔ L) ⊓ CFSG.Open.pCoreOf 2 Y = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 Y) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hLO : L ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    hLY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
  have hint : L ⊓ CFSG.Open.pCoreOf 2 Y ≤ CFSG.Open.pCoreOf 2 L :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      ((le_inf Subgroup.le_normalizer hLO).trans Subgroup.inf_normalizer_le_normalizer_inf)
      (hO2.to_le inf_le_right)
  rw [hO] at hint
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨hxAL, hxO⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨k, hk⟩ := hO2 ⟨x, hxO⟩
  have hxk : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hxL : x ∈ L := mem_of_pow_two_of_mem_sup hAL hA3 (by rwa [sup_comm]) hxk
  exact hint ⟨hxL, hxO⟩

theorem nonempty_quot_sup_equiv {A L Y : Subgroup G} (hA3 : IsPGroup 3 A)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hYA : A ≤ Subgroup.normalizer (Y : Set G))
    (hLY : L ≤ Y) (hcov : Y ≤ L ⊔ CFSG.Open.pCoreOf 2 Y) (hO : CFSG.Open.pCoreOf 2 L = ⊥) :
    letI := kerAO2_normal hAL
    letI := kerAO2_normal hYA
    Nonempty (↥(A ⊔ L) ⧸ kerAO2 A L ≃* ↥(A ⊔ Y) ⧸ kerAO2 A Y) := by
  let _ := kerAO2_normal hAL
  let _ := kerAO2_normal hYA
  set O := CFSG.Open.pCoreOf 2 Y with hOdef
  have hALY : A ⊔ L ≤ A ⊔ Y := sup_le_sup_left hLY A
  have hOY : O ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  set f : ↥(A ⊔ L) →* ↥(A ⊔ Y) ⧸ kerAO2 A Y :=
    (QuotientGroup.mk' (kerAO2 A Y)).comp (Subgroup.inclusion hALY) with hf
  have hALO : A ⊔ L ≤ Subgroup.normalizer (O : Set G) :=
    sup_le (hYA.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
      (hLY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))
  have hAYle : A ⊔ Y ≤ (A ⊔ L) ⊔ O := by
    refine sup_le (le_sup_left.trans le_sup_left) (hcov.trans ?_)
    exact sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (kerAO2 A Y) z
    have hy : (y : G) ∈ (((A ⊔ L) ⊔ O : Subgroup G) : Set G) := hAYle y.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (A ⊔ L) O hALO] at hy
    obtain ⟨x, hx, o, ho, hxo⟩ := hy
    refine ⟨⟨x, hx⟩, ?_⟩
    have hoAY : o ∈ A ⊔ Y := Subgroup.mem_sup_right (hOY ho)
    have hsplit : y = Subgroup.inclusion hALY ⟨x, hx⟩ * ⟨o, hoAY⟩ := Subtype.ext hxo.symm
    have ho1 : QuotientGroup.mk' (kerAO2 A Y) (⟨o, hoAY⟩ : ↥(A ⊔ Y)) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr ho
    rw [hsplit, map_mul, ho1, mul_one]
    rfl
  have hker : kerAO2 A L = f.ker := by
    have h1 : kerAO2 A L = ⊥ := by
      rw [kerAO2, hO, Subgroup.bot_subgroupOf]
    rw [h1, eq_comm, eq_bot_iff]
    intro x hx
    have hxO : (x : G) ∈ O := by
      have hx1 : QuotientGroup.mk' (kerAO2 A Y) (Subgroup.inclusion hALY x) = 1 :=
        MonoidHom.mem_ker.mp hx
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
      exact Subgroup.mem_subgroupOf.mp hx1
    have hbot := sup_inf_pCoreOf_eq_bot hA3 hAL hLY hO
    have hx1 : (x : G) = 1 := by
      have : (x : G) ∈ (A ⊔ L) ⊓ O := ⟨x.2, hxO⟩
      rw [hbot] at this
      exact this
    exact (Subgroup.mem_bot).mpr (Subtype.ext hx1)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)⟩

end Proof163Shape

open Proof163Shape Proof169Theta Proof1612

theorem step163TwoPowShape_of
    (h135 : Item135Simple) (h1510 : Item1510R) (h138 : Item138N) : Step163TwoPowShape := by
  intro G _ _ A c L h hO h32 Y hY hYA hLY hcov hΩ hprod
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  obtain ⟨n, hn1, hiso⟩ := h32
  have hL3 : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) := ⟨2, n, inferInstance, hn1, hiso⟩
  have hθ := theta_eq_pCore_two_of_item135Simple h135 hD (Or.inl hL3)
  have hθ' : aschbacherSolvableCore 3 ↥L = CFSG.Open.pCore 2 ↥L :=
    hθ.trans (CFSG.pCore_eq_open ↥L 2)
  have hθ1 : aschbacherSolvableCore 3 ↥L = ⊥ := by
    rw [hθ']
    rw [CFSG.Open.pCoreOf, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective] at hO
    exact hO
  have hsimp : IsSimpleGroup ↥L := by
    have e : ↥L ≃* ↥L ⧸ aschbacherSolvableCore 3 ↥L :=
      QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hθ1.symm)
    exact (MulEquiv.isSimpleGroup_congr e).mpr (isSimpleGroup_lBar hD hL3)
  have h34 : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
      CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) :=
    ⟨fun φ => false_of_l34 h φ hΩ hprod (h1510 G A c L h)
      (step169TwoBridge_of_item135Simple h135)⟩
  have h2 : 2 < n := two_lt_of_isZ3LThreeTwo hD ⟨hn1, hiso, hprod⟩ h34
  have h3 : n ≠ 3 := by
    rintro rfl
    exact not_modNine_of_inner h h138 KFacts.kSL3PiOrder3TypeC hn1 hiso hprod
      (Or.inr (by norm_num))
  refine ⟨hsimp, n, by omega, ?_⟩
  let _ := kerAO2_normal hYA
  let _ := kerAO2_normal hD.le_normalizer
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hD.card_eq]; norm_num)
  have hcov' : Y ≤ L ⊔ CFSG.Open.pCoreOf 2 Y :=
    hcov.le.trans (sup_le_sup_right inf_le_right _)
  obtain ⟨e₁⟩ := nonempty_quot_sup_equiv hA3 hD.le_normalizer hYA hLY hcov' hO
  obtain ⟨e₂⟩ := nonempty_quot_equiv_lBarA hD hθ'
  obtain ⟨e₃⟩ := hprod
  obtain ⟨η, -⟩ := exists_lBarEquiv hD.mem_thetaComponentsAt
  exact ⟨↥L ⧸ aschbacherSolvableCore 3 ↥L, inferInstance, hiso,
    ⟨e₁.symm.trans (e₂.trans (e₃.trans (MulEquiv.prodCongr (MulEquiv.refl _) η.symm)))⟩⟩

end CFSG.RankThree.PartTwo.Sec16
