module

public import CFSG.RankThree.PartTwo.Sec3.ThompsonFamilyG
import CFSG.RankThree.PartTwo.Sec20.Item20Res4ProofThompson
import CFSG.RankThree.PartTwo.Sec18.Item181ThreeProofThompson
public import CFSG.RankThree.PartTwo.Sec18.Notation
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec3
open scoped commutatorElement Pointwise

namespace Res5

section Transport

variable {X Y : Type*} [Group X] [Group Y]

theorem map_omegaG_of_injective (f : X →* Y) (hf : Function.Injective f) (J : Subgroup X) :
    (omegaG J).map f = omegaG (J.map f) := by
  ext y
  constructor
  · rintro ⟨z, ⟨hzJ, hzc, hz2⟩, rfl⟩
    refine ⟨⟨z, hzJ, rfl⟩, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, ← map_mul, hzc x hx]
    · rw [← map_mul, hz2, map_one]
  · rintro ⟨⟨z, hzJ, rfl⟩, hzc, hz2⟩
    refine ⟨z, ⟨hzJ, fun x hx => hf ?_, hf ?_⟩, rfl⟩
    · rw [map_mul, map_mul]
      exact hzc _ ⟨x, hx, rfl⟩
    · rw [map_mul, hz2, map_one]

theorem isElemTwo_map_iff (f : X →* Y) (hf : Function.Injective f) (A : Subgroup X) :
    IsElemTwo (A.map f) ↔ IsElemTwo A := by
  constructor
  · rintro ⟨hc, h2⟩
    refine ⟨fun a ha b hb => hf ?_, fun a ha => hf ?_⟩
    · rw [map_mul, map_mul]
      exact hc _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    · rw [map_mul, map_one]
      exact h2 _ ⟨a, ha, rfl⟩
  · rintro ⟨hc, h2⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hc a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, h2 a ha, map_one]

theorem map_jG_of_injective [Finite X] [Finite Y] (f : X →* Y) (hf : Function.Injective f)
    (T : Subgroup X) (i : ℕ) : (jG T i).map f = jG (T.map f) i := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr : CFSG.pRank 2 ↥(T.map f) = CFSG.pRank 2 ↥T :=
    (Res4.pRank_congr (T.equivMapOfInjective f hf) 2).symm
  rw [jG, jG, (Subgroup.gc_map_comap f).l_sSup]
  apply le_antisymm
  · refine iSup₂_le fun A hA => ?_
    refine le_sSup ⟨Subgroup.map_mono hA.1, (isElemTwo_map_iff f hf A).mpr hA.2.1, ?_⟩
    rw [Subgroup.card_map_of_injective hf, hA.2.2, hr]
  · refine sSup_le fun B hB => ?_
    have hBf : B ≤ f.range := hB.1.trans (Subgroup.map_le_range f T)
    have hBA : (B.comap f).map f = B := Subgroup.map_comap_eq_self hBf
    refine le_iSup₂_of_le (B.comap f) ?_ (le_of_eq hBA.symm)
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      have : f x ∈ T.map f := hB.1 hx
      obtain ⟨y, hy, hyx⟩ := this
      rw [← hf hyx]
      exact hy
    · rw [← isElemTwo_map_iff f hf, hBA]
      exact hB.2.1
    · rw [← Subgroup.card_map_of_injective hf, hBA, hB.2.2, hr]

end Transport

section RankOne

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem isElemTwo_zpowers {z : G} (hz : z * z = 1) : IsElemTwo (Subgroup.zpowers z) := by
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← zpow_add, ← zpow_add, add_comm]
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact hz
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_ofNat, hz2, one_zpow]

theorem omegaG_eq_jG_zero_of_omegaG_jG_one_eq_bot {R : Subgroup G} (hR2 : IsPGroup 2 R)
    (hR1 : R ≠ ⊥) (hE : omegaG (jG R 1) = ⊥) : omegaG R = jG R 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ1 : jG R 1 = ⊥ := by
    by_contra hne
    exact Sec18.Item181ThreeProof.omegaG_ne_bot (hR2.to_le (jG_le R 1)) hne hE
  have hrk : CFSG.pRank 2 ↥R ≤ 1 := by
    by_contra hlt
    push Not at hlt
    obtain ⟨A, hA⟩ := Res4.exists_mem_famG_zero R
    have hdvd : 2 ^ (CFSG.pRank 2 ↥R - 1) ∣ Nat.card A := by
      rw [hA.2.2]
      exact Nat.pow_dvd_pow 2 (by omega)
    obtain ⟨B₀, hB₀⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
    set B := B₀.map A.subtype with hB
    have hBc : Nat.card B = 2 ^ (CFSG.pRank 2 ↥R - 1) := by
      rw [hB, Subgroup.card_map_of_injective A.subtype_injective, hB₀]
    have hBA : B ≤ A := Subgroup.map_subtype_le B₀
    have hBf : B ∈ famG R 1 :=
      ⟨hBA.trans hA.1, ⟨fun a ha b hb => hA.2.1.1 a (hBA ha) b (hBA hb),
        fun a ha => hA.2.1.2 a (hBA ha)⟩, hBc⟩
    have hBle : B ≤ jG R 1 := le_jG hBf
    rw [hJ1, le_bot_iff] at hBle
    rw [hBle, Subgroup.card_bot] at hBc
    have h2 : 2 ≤ 2 ^ (CFSG.pRank 2 ↥R - 1) :=
      le_self_pow₀ (by norm_num) (by omega)
    omega
  obtain ⟨⟨z, hzZ⟩, hz1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Sec18.Item181ThreeProof.omegaG_ne_bot hR2 hR1)
  have hz1 : z ≠ 1 := fun h => hz1' (Subtype.ext h)
  have huniq : ∀ t ∈ R, t * t = 1 → t ∈ Subgroup.zpowers z := by
    intro t ht ht2
    by_contra htz
    have hzt : ∀ a ∈ Subgroup.zpowers z, ∀ b ∈ Subgroup.zpowers t, a * b = b * a := by
      intro a ha b hb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact ((Commute.zpow_zpow (hzZ.2.1 t ht) i j)).eq
    have hEl : IsElemTwo (Subgroup.zpowers z ⊔ Subgroup.zpowers t) :=
      isElemTwo_sup (isElemTwo_zpowers hzZ.2.2) (isElemTwo_zpowers ht2) hzt
    have hot : orderOf t = 2 := by
      refine orderOf_eq_prime (by rw [pow_two]; exact ht2) fun h => htz ?_
      rw [h]
      exact Subgroup.one_mem _
    have hinf : Subgroup.zpowers z ⊓ Subgroup.zpowers t = ⊥ := by
      have hdvd : Nat.card ↥(Subgroup.zpowers z ⊓ Subgroup.zpowers t) ∣ 2 := by
        rw [← hot, ← Nat.card_zpowers]
        exact Subgroup.card_dvd_of_le inf_le_right
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact Subgroup.eq_bot_of_card_eq _ h
      · exfalso
        have heq : Subgroup.zpowers z ⊓ Subgroup.zpowers t = Subgroup.zpowers t :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, Nat.card_zpowers, hot])
        apply htz
        have : t ∈ Subgroup.zpowers z ⊓ Subgroup.zpowers t := by
          rw [heq]
          exact Subgroup.mem_zpowers t
        exact this.1
    have hoz : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzZ.2.2) hz1
    have hcard := card_sup_mul_card_inf_of_commute hzt
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hoz, hot] at hcard
    have hle := card_le_two_pow_pRank (sup_le (Subgroup.zpowers_le.mpr hzZ.1)
      (Subgroup.zpowers_le.mpr ht)) hEl
    rw [hcard] at hle
    have : 2 ^ CFSG.pRank 2 ↥R ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hrk
    omega
  have hzc : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hzZ.2.2) hz1
  have hJle : jG R 0 ≤ Subgroup.zpowers z := by
    refine sSup_le fun A hA a ha => huniq a (hA.1 ha) (hA.2.1.2 a ha)
  have hΩle : omegaG R ≤ Subgroup.zpowers z := fun x hx => huniq x hx.1 hx.2.2
  have hzΩ : Subgroup.zpowers z ≤ omegaG R := Subgroup.zpowers_le.mpr hzZ
  have hJ : jG R 0 = Subgroup.zpowers z := by
    have hne := Sec18.Item181ThreeProof.jG_zero_ne_bot hR2 hR1
    obtain ⟨⟨y, hy⟩, hy1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hy1 : y ≠ 1 := fun h => hy1' (Subtype.ext h)
    have hyz : Subgroup.zpowers y = Subgroup.zpowers z := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (hJle hy)) ?_
      rw [hzc, Nat.card_zpowers]
      have hdvd : orderOf y ∣ 2 := by
        rw [← hzc]
        exact Subgroup.orderOf_dvd_natCard _ (hJle hy)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hy1
      · omega
    exact le_antisymm hJle (hyz ▸ Subgroup.zpowers_le.mpr hy)
  rw [hJ]
  exact le_antisymm hΩle hzΩ

end RankOne

theorem map_fourChar_subgroupOf {G : Type*} [Group G] [Finite G] {R X : Subgroup G}
    (hRX : R ≤ X) (i : Fin 4) (hi : i ≠ 3) :
    (Sec18.fourChar (R.subgroupOf X) i).map X.subtype = Sec18.fourChar R i := by
  have hR : (R.subgroupOf X).map X.subtype = R := Subgroup.map_subgroupOf_eq_of_le hRX
  match i, hi with
  | 0, _ =>
    rw [Sec18.Item181ThreeProof.fourChar_zero, Sec18.Item181ThreeProof.fourChar_zero,
      map_omegaG_of_injective _ X.subtype_injective, hR]
  | 1, _ =>
    rw [Sec18.Item181ThreeProof.fourChar_one, Sec18.Item181ThreeProof.fourChar_one,
      map_jG_of_injective _ X.subtype_injective, hR]
  | 2, _ =>
    rw [Sec18.Item181ThreeProof.fourChar_two, Sec18.Item181ThreeProof.fourChar_two,
      map_omegaG_of_injective _ X.subtype_injective,
      map_jG_of_injective _ X.subtype_injective, hR]
  | 3, h => exact absurd rfl h

end Res5

end CFSG.RankThree.PartTwo.Sec20
