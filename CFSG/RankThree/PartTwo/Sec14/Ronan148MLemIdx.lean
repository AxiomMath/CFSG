module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148M

theorem le_of_isPerfect_of_card_dvd_three_mul {G : Type*} [Group G] [Finite G] {K H : Subgroup G}
    (hKH : K ≤ H) (hHN : H ≤ Subgroup.normalizer (K : Set G))
    (hcard : Nat.card H ∣ 3 * Nat.card K) (hH : Group.IsPerfect ↥H) : H ≤ K := by
  have hnorm : (K.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have hcardK : Nat.card (K.subgroupOf H) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
  have hmul : Nat.card (K.subgroupOf H) * (K.subgroupOf H).index = Nat.card H :=
    Subgroup.card_mul_index (H := K.subgroupOf H)
  rw [hcardK] at hmul
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hdvd3 : (K.subgroupOf H).index ∣ 3 := by
    refine Nat.dvd_of_mul_dvd_mul_left hpos ?_
    rw [hmul, mul_comm (Nat.card K) 3]
    exact hcard
  have hQcard : Nat.card (↥H ⧸ K.subgroupOf H) ∣ 3 ^ 1 := by
    rw [pow_one, ← Subgroup.index_eq_card]
    exact hdvd3
  have hP : IsPGroup 3 (↥H ⧸ K.subgroupOf H) := IsPGroup.of_card_dvd_pow hQcard
  have hnil : Group.IsNilpotent (↥H ⧸ K.subgroupOf H) := IsPGroup.isNilpotent hP
  have hsub : Subsingleton (↥H ⧸ K.subgroupOf H) := by
    refine not_nontrivial_iff_subsingleton.mp fun hnt => ?_
    exact Group.IsPerfect.not_isNilpotent (↥H ⧸ K.subgroupOf H) hnil
  intro h hh
  have hmem : (⟨h, hh⟩ : ↥H) ∈ K.subgroupOf H :=
    (QuotientGroup.eq_one_iff _).mp (Subsingleton.elim _ _)
  exact Subgroup.mem_subgroupOf.mp hmem

end CFSG.RankThree.PartTwo.Sec14.Ronan148M
