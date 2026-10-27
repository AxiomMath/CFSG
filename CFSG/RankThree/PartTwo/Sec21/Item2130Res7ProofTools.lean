module

import CFSG.RankThree.PartTwo.Sec21.Item2119End3Proof2125Unique
import CFSG.RankThree.PartTwo.Sec10.Item101
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
public import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofLocal
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res6ProofAct
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res6ProofMat

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2130Res7Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly (IsElemAbelian)
open Item2130Res6Proof Item211Res2Proof

variable {G : Type} [Group G] [Finite G]

theorem exists_pow_three_part {H : Type*} [Group H] [Finite H] (y : H) :
    ∃ r : ℕ, r % 3 = 1 ∧ ∃ k : ℕ, (y ^ r) ^ (3 ^ k) = 1 := by
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' 3 (by norm_num)
  refine ⟨m * (m % 3), ?_, k, ?_⟩
  · have hm3 : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rw [Nat.mul_mod, Nat.mod_mod]
    rcases hm3 with h | h <;> rw [h]
  · rw [← pow_mul, show m * (m % 3) * 3 ^ k = (3 ^ k * m) * (m % 3) by ring, pow_mul, ← hn,
      pow_orderOf_eq_one, one_pow]

omit [Finite G] in
theorem pow_eq_self_of_pow_three {M : Type*} [Monoid M] {x : M} (hx : x ^ 3 = 1) {r : ℕ}
    (hr : r % 3 = 1) : x ^ r = x := by
  rw [← Nat.div_add_mod r 3, hr, pow_add, pow_mul, hx, one_pow, one_mul, pow_one]

theorem eq_one_of_mk_eq_one {Y : Subgroup G} {t : Y} (ht : (t : lBar Y) = 1) {k : ℕ}
    (htk : t ^ (3 ^ k) = 1) : t = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htθ : t ∈ aschbacherSolvableCore 3 Y := (QuotientGroup.eq_one_iff t).mp ht
  have hcop := (solvable_prime_complement_core_characterization (H := Y) Nat.prime_three).2.2.1
  have h1 : orderOf t ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one htk
  have h2 : orderOf (⟨t, htθ⟩ : aschbacherSolvableCore 3 Y) ∣
      Nat.card (aschbacherSolvableCore 3 Y) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
  rcases j with _ | j
  · rw [pow_zero] at hj
    exact orderOf_eq_one_iff.mp hj
  · exfalso
    apply hcop
    rw [hj] at h2
    exact (dvd_pow_self 3 (Nat.succ_ne_zero j)).trans h2

theorem exists_lift_fixed {Y X : Subgroup G} (hX : IsPGroup 3 X)
    (hXN : X ≤ Subgroup.normalizer (Y : Set G)) (z : lBar Y)
    (hz : ∀ (x : G) (hx : x ∈ X), barHom Y ⟨x, hXN hx⟩ z = z) :
    ∃ y : Y, (y : lBar Y) = z ∧ ∀ x ∈ X, x * (y : G) * x⁻¹ = y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ι : X →* Subgroup.normalizer (Y : Set G) := Subgroup.inclusion hXN with hι
  obtain ⟨y, hy, hfix⟩ :=
    CFSG.OrderReductions.FixedPointLifting.exists_fixed_lift_of_coprime_kernel 3 hX
      (Y.normalizerMonoidHom.comp ι) ((barHom Y).comp ι)
      (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)) (QuotientGroup.mk'_surjective _)
      (by
        rw [QuotientGroup.ker_mk']
        exact (solvable_prime_complement_core_characterization (H := Y) Nat.prime_three).2.2.1)
      (fun _ _ => rfl) z (fun x => hz x x.2)
  exact ⟨y, hy, fun x hx => congrArg Subtype.val (hfix ⟨x, hx⟩)⟩

theorem mem_of_commute_of_pow_three {A : Subgroup G} (hAe : IsElemAbelian 3 A)
    (hAmax : ∀ B : Subgroup G, IsElemAbelian 3 B → A ≤ B → B = A) {y : G} (hy3 : y ^ 3 = 1)
    (hyA : ∀ a ∈ A, y * a = a * y) : y ∈ A := by
  obtain ⟨hB, -⟩ := Item2119End3Proof.isElemAbelian_sup_zpowers hAe hy3 hyA
  rw [← hAmax _ hB le_sup_left]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)

theorem exists_lift_mem {A Y : Subgroup G} (hAe : IsElemAbelian 3 A)
    (hAmax : ∀ B : Subgroup G, IsElemAbelian 3 B → A ≤ B → B = A)
    (hAN : A ≤ Subgroup.normalizer (Y : Set G)) {z : lBar Y} (hz3 : z ^ 3 = 1)
    (hz : ∀ (a : G) (ha : a ∈ A), barHom Y ⟨a, hAN ha⟩ z = z) :
    ∃ d : Y, (d : G) ∈ A ∧ (d : lBar Y) = z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAe.2 g g.2)⟩
  obtain ⟨y, hy, hyA⟩ := exists_lift_fixed hA hAN z hz
  obtain ⟨r, hr, k, hk⟩ := exists_pow_three_part y
  have hyr : ((y ^ r : Y) : lBar Y) = z := by
    rw [QuotientGroup.mk_pow, hy, pow_eq_self_of_pow_three hz3 hr]
  have hyr3 : (y ^ r) ^ 3 = 1 := by
    refine eq_one_of_mk_eq_one (k := k) ?_ ?_
    · rw [QuotientGroup.mk_pow, hyr, hz3]
    · rw [← pow_mul, mul_comm, pow_mul, hk, one_pow]
  refine ⟨y ^ r, mem_of_commute_of_pow_three hAe hAmax ?_ fun a ha => ?_, hyr⟩
  · have := congrArg Subtype.val hyr3
    simpa using this
  · have h1 : a * (y : G) * a⁻¹ = y := hyA a ha
    have hc : Commute (y : G) a := by
      calc (y : G) * a = a * (y : G) * a⁻¹ * a := by rw [h1]
        _ = a * y := by group
    rw [Subgroup.coe_pow]
    exact (hc.pow_left r).eq

omit [Finite G] in
theorem mem_zpowers_pow_of_lt_three {x : G} (hx3 : x ^ 3 = 1) {i : ℕ} (hi0 : i ≠ 0)
    (hi3 : i < 3) : x ∈ Subgroup.zpowers (x ^ i) := by
  have hi1 : 1 ≤ i := Nat.pos_of_ne_zero hi0
  interval_cases i
  · rw [pow_one]
    exact Subgroup.mem_zpowers x
  · have h : (x ^ 2) ^ 2 = x := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hx3, one_mul, pow_one]
    exact Subgroup.mem_zpowers_iff.mpr ⟨2, by rw [zpow_two, ← pow_two]; exact h⟩

theorem exists_mem_normalizer_of_conj_mem {A Y : Subgroup G} (hA : IsPGroup 3 A)
    (hAN : A ≤ Subgroup.normalizer (Y : Set G)) {y : G}
    (hy : ∀ a ∈ A, y * a * y⁻¹ ∈ A ⊔ (aschbacherSolvableCore 3 Y).map Y.subtype) :
    ∃ t ∈ (aschbacherSolvableCore 3 Y).map Y.subtype,
      t * y ∈ Subgroup.normalizer (A : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set T := (aschbacherSolvableCore 3 Y).map Y.subtype with hT
  have hT3 : ¬ 3 ∣ Nat.card T := by
    rw [hT, Subgroup.card_map_of_injective Y.subtype_injective]
    exact (solvable_prime_complement_core_characterization (H := Y) Nat.prime_three).2.2.1
  have hNT : ∀ g ∈ Subgroup.normalizer (Y : Set G), g ∈ Subgroup.normalizer (T : Set G) := by
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun t ht => ?_
    obtain ⟨t', ht', rfl⟩ := ht
    have h1 : Y.normalizerMonoidHom ⟨g, hg⟩ t' ∈ aschbacherSolvableCore 3 Y := by
      rw [← map_aschbacherSolvableCore (Y.normalizerMonoidHom ⟨g, hg⟩)]
      exact ⟨t', ht', rfl⟩
    exact ⟨_, h1, rfl⟩
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := fun a ha => hNT a (hAN ha)
  have hinf : A ⊓ T = ⊥ := by
    have h1 : Nat.card (A ⊓ T : Subgroup G) ∣ Nat.card A := Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card (A ⊓ T : Subgroup G) ∣ Nat.card T := Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨k, hk⟩ := hA.exists_card_eq
    rw [hk] at h1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
    rcases j with _ | j
    · exact Subgroup.eq_bot_of_card_eq _ (by simpa using hj)
    · exfalso
      rw [hj] at h2
      exact hT3 ((dvd_pow_self 3 (Nat.succ_ne_zero j)).trans h2)
  have hcardM : Nat.card (A ⊔ T : Subgroup G) = Nat.card A * Nat.card T := by
    have := Sec6.card_sup_mul_card_inf hAT
    rwa [hinf, Subgroup.card_bot, mul_one] at this
  set A' := A.map (MulAut.conj y).toMonoidHom with hA'
  have hA'M : A' ≤ A ⊔ T := by
    rintro _ ⟨a, ha, rfl⟩
    exact hy a ha
  have hcardA' : Nat.card A' = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj y).injective
  have hsyl : ∀ P : Subgroup G, P ≤ A ⊔ T → IsPGroup 3 P → Nat.card P = Nat.card A →
      CFSG.ABGLocalTools.IsSylowOf 3 P (A ⊔ T) := by
    intro P hPM hP hcard
    refine CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hPM, hP, ?_⟩
    have h1 := Subgroup.relIndex_mul_card P (A ⊔ T)
    rw [inf_eq_left.mpr hPM, hcard, hcardM, mul_comm (Nat.card A)] at h1
    have h2 : P.relIndex (A ⊔ T) = Nat.card T := Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
    rw [h2]
    exact hT3
  obtain ⟨m, hmM, hm⟩ := Sec13.Item134SylowBarProof.exists_conj_of_isSylowOf
    (hsyl A' hA'M (hA.map _) hcardA') (hsyl A le_sup_left hA rfl)
  have hmM' : m ∈ ((A ⊔ T : Subgroup G) : Set G) := hmM
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A T hAT] at hmM'
  obtain ⟨a₀, ha₀, t₀, ht₀, rfl⟩ := hmM'
  refine ⟨t₀, ht₀, Subgroup.mem_normalizer_fintype fun x hx => ?_⟩
  have hx' : (a₀ * t₀) * (y * x * y⁻¹) * (a₀ * t₀)⁻¹ ∈ A := by
    rw [hm]
    exact ⟨y * x * y⁻¹, ⟨x, hx, rfl⟩, rfl⟩
  have e : t₀ * y * x * (t₀ * y)⁻¹ =
      a₀⁻¹ * ((a₀ * t₀) * (y * x * y⁻¹) * (a₀ * t₀)⁻¹) * a₀ := by
    group
  rw [e]
  exact A.mul_mem (A.mul_mem (A.inv_mem ha₀) hx') ha₀

variable {A E U L U₀ Y : Subgroup G} {c b : G}

theorem mem_inf_of_mem (hcfg : Config2130 G A E U c L) (hC : Choice2130 A E c L b U₀ Y)
    (hcY : c ∉ Y) {d : G} (hdA : d ∈ A) (hdY : d ∈ Y) : d ∈ A ⊓ L := by
  have hAe : IsElemAbelian 3 A := hcfg.pair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hpairs := mem_lThreeStarPairs_iff.mp hcfg.pair.mem_pair
  have hcA : c ∈ A := hcfg.pair.mem_E.2 hpairs.1.1
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hAB : A = Subgroup.zpowers c ⊔ (A ⊓ L) :=
    Item2130Proof.eq_zpowers_sup hcA inf_le_left (fun h => hcfg.not_mem h.2) hcfg.card_eq
  by_contra hdB
  have hd' : d ∈ Subgroup.zpowers c ⊔ (A ⊓ L) := hAB ▸ hdA
  obtain ⟨k, β₀, hβ₀, hdk⟩ := Sec10.exists_zpow_mul_of_mem_sup_zpowers (H := A ⊓ L)
    (fun h hh => hcomm h (Subgroup.mem_inf.mp hh).1 c hcA) hd'
  obtain ⟨i, hi3, hci⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers hc3
    (Subgroup.zpow_mem_zpowers c k)
  rw [hci] at hdk
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hdk
    exact hdB (hdk ▸ hβ₀)
  have hβY : ∀ β ∈ A ⊓ L, β ^ i ∈ Y := by
    intro β hβ
    obtain ⟨w, hwN, hwB, hwc⟩ := Choice2130.exists_conj hcfg hC hβ
    have hwd : w * d * w⁻¹ = d * β ^ i := by
      have hcβ : Commute c β := hcomm c hcA β hβ.1
      have h1 : w * c ^ i * w⁻¹ = (c * β) ^ i := by
        rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hwc]
      calc w * d * w⁻¹ = (w * c ^ i * w⁻¹) * (w * β₀ * w⁻¹) := by rw [hdk]; group
        _ = (c * β) ^ i * β₀ := by rw [h1, hwB β₀ hβ₀]
        _ = c ^ i * β ^ i * β₀ := by rw [hcβ.mul_pow]
        _ = c ^ i * β₀ * β ^ i := by
            rw [mul_assoc, mul_assoc, (Commute.pow_left (hcomm β hβ.1 β₀ hβ₀.1) i).eq]
        _ = d * β ^ i := by rw [hdk]
    have h2 : w * d * w⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hwN d).mp hdY
    rw [hwd] at h2
    have h3 := Y.mul_mem (Y.inv_mem hdY) h2
    rwa [inv_mul_cancel_left] at h3
  have hBY : ∀ β ∈ A ⊓ L, β ∈ Y := fun β hβ =>
    (Subgroup.zpowers_le.mpr (hβY β hβ)) (mem_zpowers_pow_of_lt_three (hAe.2 β hβ.1) hi0 hi3)
  have hciY : c ^ i ∈ Y := by
    have : c ^ i = d * β₀⁻¹ := by rw [hdk]; group
    rw [this]
    exact Y.mul_mem hdY (Y.inv_mem (hBY β₀ hβ₀))
  exact hcY ((Subgroup.zpowers_le.mpr hciY) (mem_zpowers_pow_of_lt_three hc3 hi0 hi3))

end CFSG.RankThree.PartTwo.Sec21.Item2130Res7Proof
