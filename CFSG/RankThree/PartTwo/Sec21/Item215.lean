module

public import CFSG.RankThree.PartTwo.Sec21.PairExistence
public import CFSG.RankThree.PartTwo.Sec21.Membership
public import CFSG.RankThree.PartTwo.Sec4.Statements
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item215 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → ∀ U' ∈ fourGroupsMinus E,
      ∃ b ∈ E ⊓ Subgroup.centralizer (U' : Set G), b ∉ Subgroup.zpowers c ∧
        ∃ K ∈ lThreeStarAt A b, (b, K) ∈ lThreeStarPairs A E U'

variable {G : Type} [Group G]

theorem mem_zpowers_of_mem_zpowers [Finite G] {b c : G} (hc3 : c ^ 3 = 1) (hb1 : b ≠ 1)
    (hb : b ∈ Subgroup.zpowers c) : c ∈ Subgroup.zpowers b := by
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hb
    exact hb1 hb
  have hoc : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hle : Subgroup.zpowers b ≤ Subgroup.zpowers c := (Subgroup.zpowers_le).mpr hb
  have hob : orderOf b ∣ 3 := by
    rw [← hoc, ← Nat.card_zpowers, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le hle
  have hob3 : orderOf b = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hob with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hb1
    · exact h
  have heq : Subgroup.zpowers b = Subgroup.zpowers c := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Nat.card_zpowers, Nat.card_zpowers, hob3, hoc]
  rw [heq]
  exact Subgroup.mem_zpowers c

theorem rank3II_21_5_of (h45 : Sec4.Item4_5) (h49 : Sec4.Item4_9) : Item215 := by
  intro G _ _ A E U c L hpair U' hU'
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hG := hpair.standing
  have hE := hpair.mem_E
  have hEmem := hE.1
  have hEab := hEmem.1
  have hA := hpair.mem_S
  obtain ⟨hU2, hU1⟩ := Sec6.isPGroup_two_and_ne_bot_of_mem_fourGroups hU'.1
  have hB9 := Sec6.card_inf_centralizer_of_mem_fourGroupsMinus
    (Late.isE27_of_mem_partTwoE hEmem) hU'
  have hBab : CFSG.Assembly.IsElemAbelian 3 (E ⊓ Subgroup.centralizer (U' : Set G)) :=
    Sec5.isElemAbelian_of_le hEab inf_le_left
  have hcE : c ∈ E := (mem_lThreeStarPairs_iff.mp hpair.mem_pair).1.1
  have hc3 : c ^ 3 = 1 := hEab.2 c hcE
  obtain ⟨e, heB, he1, hec⟩ : ∃ e ∈ E ⊓ Subgroup.centralizer (U' : Set G), e ≠ 1 ∧
      (c ∈ E ⊓ Subgroup.centralizer (U' : Set G) → e = c) := by
    by_cases hcB : c ∈ E ⊓ Subgroup.centralizer (U' : Set G)
    · exact ⟨c, hcB, (mem_lThreeStarPairs_iff.mp hpair.mem_pair).2.1, fun _ => rfl⟩
    · have hB1 : E ⊓ Subgroup.centralizer (U' : Set G) ≠ ⊥ := fun h => by
        rw [h, Subgroup.card_bot] at hB9
        norm_num at hB9
      obtain ⟨e, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB1
      exact ⟨e, e.2, fun h => he1 (Subtype.ext h), fun h => absurd h hcB⟩
  have hF1 : Subgroup.zpowers e ≠ ⊥ := fun h => he1 (Subgroup.zpowers_eq_bot.mp h)
  obtain ⟨b, hbB, hb1, hV⟩ := Sec6.exists_commutator_inf_centralizer_ne_bot hG.charTwoType hU2
    hU1 hBab hB9.ge inf_le_right (Subgroup.zpowers_le.mpr heB) hF1
  obtain ⟨K, hK, hUK, hKU, hVK, hKV⟩ := Sec6.exists_pair_of_mem_fourGroupsMinus hG h45 h49 hA hE
    hU' (Subgroup.zpowers_le.mpr heB.1) (Subgroup.zpowers_le.mpr heB.2) hbB.1 hbB.2 hb1 hV
  have hbc : b ∉ Subgroup.zpowers c := by
    intro hb
    have hcb := mem_zpowers_of_mem_zpowers hc3 hb1 hb
    by_cases hcB : c ∈ E ⊓ Subgroup.centralizer (U' : Set G)
    · apply hV
      rw [hec hcB, eq_bot_iff, Subgroup.commutator_le]
      intro x hx y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hcb
      have hxb : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
      have hcomm : Commute x ((b ^ j) ^ k) := ((Commute.zpow_right hxb j).zpow_right k)
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm.eq
    · apply hcB
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hcb
      exact (E ⊓ Subgroup.centralizer (U' : Set G)).zpow_mem hbB j
  have hbA : b ∈ A := hE.2 hbB.1
  have hAN := Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG.toTheoremFourHyp hA.1.1 hbA hb1
  have hKb : K ∈ thetaComponentsAt 3 b := (lZeroStarAt_subset A b) hK
  have hVN := lThreeV_le_normalizer (U := U') hE.2 hAN hKb
  have hVe : ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U' : Set G)) ⊓
      Subgroup.centralizer {b}, Subgroup.zpowers e⁆ ≤ lThreeV E U' b :=
    (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr heB)).trans
      (sixTwelveV_le_lThreeV E U' b)
  have hpairK : (b, K) ∈ lThreeStarPairs A E U' := by
    refine ⟨hbB, hb1, hK, hUK, hVN, hKU, le_antisymm ?_ ?_⟩
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp hVN
    · calc K = _ := hKV.symm
        _ ≤ ⁅K, lThreeV E U' b⁆ := Subgroup.commutator_mono le_rfl hVe
  exact ⟨b, hbB, hbc, K, mem_lThreeStarAt_of_mem_lThreeStarPairs hE hU'.1 hpairK, hpairK⟩

end CFSG.RankThree.PartTwo.Sec21
