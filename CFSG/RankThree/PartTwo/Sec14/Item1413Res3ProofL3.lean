module

import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec13.Notation
public import CFSG.RankThree.PartTwo.Sec15.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

@[expose] def KS1419LThreePi : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsLThreePi X →
    ∀ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 9 →
      (∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
        ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁) →
      ∀ R : Subgroup X, IsPGroup 2 R → R ≠ ⊥ → E ≤ Subgroup.normalizer (R : Set X) →
        Nat.card (E ⊓ Subgroup.centralizer (R : Set X) : Subgroup X) = 3

namespace Proof1413Res3

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_mem_of_odd {H : Type*} [Group H] {P K : Subgroup H} (hP : IsPGroup 2 P)
    (hK : ¬ 2 ∣ Nat.card K) {x : H} (hxP : x ∈ P) (hxK : x ∈ K) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have h1 : orderOf x ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    have := congrArg Subtype.val hk
    simpa using this
  have h2 : orderOf x ∣ Nat.card K := by
    rw [show orderOf x = orderOf (⟨x, hxK⟩ : K) from Subgroup.orderOf_coe ⟨x, hxK⟩]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card K) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hK)
  have h3 : orderOf x ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem isHyperplane_of_mem {A B L : Subgroup G} {c y : G} (h27 : Nat.card A = 27)
    (hc : orderOf c = 3) (hcL : c ∉ L) (hBA : B ≤ A) (hne : B ≠ A) (hcB : c ∈ B) (hyB : y ∈ B)
    (hyL : y ∈ L) (hy1 : y ≠ 1) : IsHyperplane A B := by
  have hle : Subgroup.closure ({c, y} : Set G) ≤ B := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hcB
    · exact hyB
  have hgt : 3 < Nat.card (Subgroup.closure ({c, y} : Set G)) := by
    have hlt : Subgroup.zpowers c < Subgroup.closure ({c, y} : Set G) := by
      refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr (Subgroup.subset_closure
        (Set.mem_insert c _))) fun h => ?_
      have hy : y ∈ Subgroup.zpowers c := h ▸ Subgroup.subset_closure
        (Set.mem_insert_of_mem c (Set.mem_singleton y))
      have h1 : y ∈ L ⊓ Subgroup.zpowers c := ⟨hyL, hy⟩
      rw [Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hc hcL, Subgroup.mem_bot] at h1
      exact hy1 h1
    have h3 : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, hc]
    rw [← h3]
    exact Subgroup.card_lt_of_lt hlt
  have hdvd1 : Nat.card (Subgroup.closure ({c, y} : Set G)) ∣ Nat.card B :=
    Subgroup.card_dvd_of_le hle
  have hdvd2 : Nat.card B ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← h27]
    exact Subgroup.card_dvd_of_le hBA
  obtain ⟨k₂, hk₂, hk₂'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd2
  have hk₂3 : k₂ ≠ 3 := by
    rintro rfl
    exact hne (Subgroup.eq_of_le_of_card_ge hBA (by rw [hk₂', h27]; norm_num))
  have hle2 := Nat.le_of_dvd (by rw [hk₂']; positivity) hdvd1
  refine ⟨hBA, ?_⟩
  rw [h27, hk₂']
  interval_cases k₂
  · rw [hk₂'] at hle2; omega
  · rw [hk₂'] at hle2; omega
  · norm_num
  · exact absurd rfl hk₂3

end Proof1413Res3

end CFSG.RankThree.PartTwo.Sec14
