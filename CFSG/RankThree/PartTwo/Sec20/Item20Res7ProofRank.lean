module

import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank
import CFSG.RankThree.Theta.ThreeCoreComponentNormalization
import CFSG.RankThree.PartTwo.Sec12.Item123Inputs
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec18.Item186a
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.BorelTits.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

namespace Res7

variable {G : Type} [Group G] [Finite G]

theorem four_le_localRank_of_quotient {X : Subgroup G} (hQ : CFSG.Open.pCoreOf 2 X ≠ ⊥)
    (V : Subgroup (X ⧸ CFSG.pCore 2 X)) (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hVe : ∀ v ∈ V, v ^ 3 = 1) (hV : 81 ≤ Nat.card V) :
    4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 G := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := CFSG.pCore 2 X with hN
  set π := QuotientGroup.mk' N with hπ
  have hN2 : IsPGroup 2 N := CFSG.pCore_isPGroup
  have hN3 : ¬ 3 ∣ Nat.card N := by
    obtain ⟨k, hk⟩ := hN2.exists_card_eq
    rw [hk]
    intro h
    have := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at this
  have hV3 : IsPGroup 3 V := fun v => ⟨1, Subtype.ext (by simpa using hVe v v.2)⟩
  have hker : Nat.Coprime 3 (Nat.card π.ker) := by
    rw [hπ, QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3
  obtain ⟨R, hR3, ⟨eR⟩⟩ := CFSG.RankThreeCoreUniqueness.Helpers.coprime_kernel_lifts_pSubgroup 3
    Nat.prime_three π (QuotientGroup.mk'_surjective N) hker V hV3
  have hRcomm : ∀ a b : R, a * b = b * a := fun a b => eR.injective (by
    rw [map_mul, map_mul]
    exact Subtype.ext (hVc _ (eR a).2 _ (eR b).2))
  have hRe : ∀ a : R, a ^ 3 = 1 := fun a => eR.injective (by
    rw [map_pow, map_one]
    exact Subtype.ext (hVe _ (eR a).2))
  obtain ⟨r, hr⟩ := hR3.exists_card_eq
  have hr4 : 4 ≤ r := by
    have h81 : 81 ≤ 3 ^ r := by
      rw [← hr, Nat.card_congr eR.toEquiv]
      exact hV
    by_contra h
    push Not at h
    interval_cases r <;> norm_num at h81
  obtain ⟨R₄, hR₄⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 4) (G := R)
    (by rw [hr]; exact pow_dvd_pow 3 hr4)
  set X₄ := (R₄.map R.subtype).map X.subtype with hX₄
  have hX₄card : Nat.card X₄ = 3 ^ 4 := by
    rw [hX₄, Subgroup.card_map_of_injective X.subtype_injective,
      Subgroup.card_map_of_injective R.subtype_injective, hR₄]
  have hX₄mem : ∀ a ∈ X₄, ∃ a' : R, (((a' : X) : G)) = a := by
    rintro _ ⟨_, ⟨a', -, rfl⟩, rfl⟩
    exact ⟨a', rfl⟩
  have hX₄c : IsMulCommutative X₄ := ⟨⟨fun a b => Subtype.ext (by
    obtain ⟨a', ha'⟩ := hX₄mem a a.2
    obtain ⟨b', hb'⟩ := hX₄mem b b.2
    change (a : G) * b = b * a
    rw [← ha', ← hb']
    exact congrArg (fun z : R => ((z : X) : G)) (hRcomm a' b'))⟩⟩
  have hX₄e : ∀ a ∈ X₄, a ^ 3 = 1 := by
    intro a ha
    obtain ⟨a', ha'⟩ := hX₄mem a ha
    rw [← ha']
    exact congrArg (fun z : R => ((z : X) : G)) (hRe a')
  have hX₄N : X₄ ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    (Subgroup.map_subtype_le _).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
  exact CFSG.RankThree.Theta.le_localRank_of_le_normalizer (by norm_num) hQ
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) hX₄c hX₄e hX₄card hX₄N

omit [Finite G] in
theorem card_sup_zpowers [Finite G] (Y : Subgroup G) {y : G} (hy : orderOf y = 3) (hyY : y ∉ Y)
    (hcomm : ∀ z ∈ Y, z * y = y * z) :
    Nat.card (Y ⊔ Subgroup.zpowers y : Subgroup G) = Nat.card Y * 3 := by
  have hYN : Y ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G) := fun z hz =>
    Sec12.mem_normalizer_zpowers_of_commute (hcomm z hz)
  have h1 := Sec6.card_sup_mul_card_inf hYN
  have hinf : Y ⊓ Subgroup.zpowers y = ⊥ := by
    have hdvd : Nat.card (Y ⊓ Subgroup.zpowers y : Subgroup G) ∣ 3 := by
      rw [← hy, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact Subgroup.card_eq_one.mp h
    · exfalso
      have heq : Y ⊓ Subgroup.zpowers y = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, Nat.card_zpowers, hy])
      have hy' : y ∈ Y ⊓ Subgroup.zpowers y := by
        rw [heq]
        exact Subgroup.mem_zpowers y
      exact hyY hy'.1
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hy] at h1
  exact h1

omit [Finite G] in
theorem mem_pCoreOf_of_forall_comm_of_simple {J : Subgroup G}
    (hsimple : IsSimpleGroup (↥J ⧸ CFSG.pCore 2 ↥J))
    (hperf : Group.IsPerfect (↥J ⧸ CFSG.pCore 2 ↥J)) {y : G} (hy : y ∈ J)
    (hc : ∀ z ∈ J, y * z * y⁻¹ * z⁻¹ ∈ CFSG.Open.pCoreOf 2 J) : y ∈ CFSG.Open.pCoreOf 2 J := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥J) with hπ
  have hZ : Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J))
      with h | h
    · exact h
    · exfalso
      have : Nontrivial (↥J ⧸ CFSG.pCore 2 ↥J) := hsimple.toNontrivial
      have hcomm : IsMulCommutative (↥J ⧸ CFSG.pCore 2 ↥J) :=
        ⟨⟨fun a b => Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a⟩⟩
      exact Group.IsPerfect.not_isMulCommutative (↥J ⧸ CFSG.pCore 2 ↥J) hcomm
  have hyc : π ⟨y, hy⟩ ∈ Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥J) w
    have h1 : (⟨y, hy⟩ * z * (⟨y, hy⟩ : ↥J)⁻¹ * z⁻¹ : ↥J) ∈ CFSG.pCore 2 ↥J :=
      (Sec18.mem_pCore_iff_mem_pCoreOf _).mpr (hc z z.2)
    have h2 : π (⟨y, hy⟩ * z * (⟨y, hy⟩ : ↥J)⁻¹ * z⁻¹) = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    have h3 : π ⟨y, hy⟩ * π z = π z * π ⟨y, hy⟩ := by
      calc π ⟨y, hy⟩ * π z = (π ⟨y, hy⟩ * π z * (π ⟨y, hy⟩)⁻¹ * (π z)⁻¹) * π z * π ⟨y, hy⟩ := by
            group
        _ = π z * π ⟨y, hy⟩ := by rw [h2, one_mul]
    exact h3.symm
  rw [hZ, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hyc
  exact (Sec18.mem_pCore_iff_mem_pCoreOf _).mp hyc

end Res7

end CFSG.RankThree.PartTwo.Sec20
