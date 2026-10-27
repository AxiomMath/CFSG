module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowTools

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

theorem pRank_three_eq_one_of_card {S : Type} [Group S] [Finite S] (h3 : 3 ∣ Nat.card S)
    (h9 : ¬ 9 ∣ Nat.card S) : CFSG.Open.pRank 3 (⊤ : Subgroup S) = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply le_antisymm
  · refine CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
    have hpE : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hpE
    have hdvd : 3 ^ m ∣ Nat.card S := hm ▸ Subgroup.card_subgroup_dvd_card E
    rw [hm]
    by_contra hlt
    have hm2 : 2 ≤ m := by
      by_contra h
      have : m ≤ 1 := by omega
      exact hlt (Nat.pow_le_pow_right (by norm_num) this)
    exact h9 ((pow_dvd_pow 3 hm2).trans hdvd)
  · obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3
    refine CFSG.SectionRank.le_pRank (by norm_num) (E := Subgroup.zpowers g) le_top ?_
      (k := 1) ?_
    · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
      · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
      · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
          show g ^ 3 = 1 by rw [← hg]; exact pow_orderOf_eq_one g, one_zpow]
    · rw [Nat.card_zpowers, hg, pow_one]

theorem listRow_of_card {S : Type} [Group S] [Finite S] (h3 : 3 ∣ Nat.card S)
    (h9 : ¬ 9 ∣ Nat.card S) : ListRow S :=
  listRow_of_pRank_eq_one (pRank_three_eq_one_of_card h3 h9)

theorem listRow_of_pRank_le_one {S : Type} [Group S] [Finite S]
    (h : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 1) : ListRow S := by
  intro z hz _
  left
  refine le_antisymm h ?_
  refine CFSG.SectionRank.le_pRank (by norm_num) (E := Subgroup.zpowers z) le_top ?_ (k := 1) ?_
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        show z ^ 3 = 1 by rw [← hz]; exact pow_orderOf_eq_one z, one_zpow]
  · rw [Nat.card_zpowers, hz, pow_one]

end CFSG.RankThree.PartTwo.Sec4.RonanK432
