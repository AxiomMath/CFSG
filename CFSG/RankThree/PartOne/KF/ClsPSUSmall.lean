module

public import CFSG.RankThree.PartOne.KF.ClsSUUpper
public import CFSG.RankThree.PartOne.KF.ClsSpUpper
public import CFSG.RankThree.PartOne.KF.ClsSU3

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.KFU CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.Census

theorem psu_three_false {G : Type} [Group G] [Finite G] {p : ℕ} {L A₀ F : Subgroup G}
    (h : Table123Generic p L A₀ F) {f : ℕ}
    (hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 2 f) : False := by
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmodel
  have hp := h.prime
  have hp5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := f * 2)
      (by rw [Fintype.card_eq_nat_card, hK, pow_mul])
  have hrank := h.localRank_eq_two_of_mulEquiv e
  have hgcd : ¬ p ∣ Nat.gcd 3 (2 ^ f + 1) := fun hd => by
    have := Nat.le_of_dvd (by norm_num) (hd.trans (Nat.gcd_dvd_left _ _))
    omega
  have h2 := localRank_statedProj_statedSU_le hK (by norm_num : 1 ≤ 3) hp hp2 hgcd
  have h3 := localRank_statedSU_three_le_one hK hp hp2
  omega

theorem psu_four_row {G : Type} [Group G] [Finite G] {p : ℕ} {L A₀ F : Subgroup G}
    (h : Table123Generic p L A₀ F) {f : ℕ}
    (hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 4 2 f) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ 12 ∧ r ≠ 11 ∧ RowModel p L r := by
  have hmodel' := hmodel
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmodel'
  have hf1 : 1 ≤ f := hadm.2.1
  have hp := h.prime
  have hp5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := f * 2)
      (by rw [Fintype.card_eq_nat_card, hK, pow_mul])
  by_cases hq : p ∣ 2 ^ f - 1
  · exact ⟨5, by norm_num, by norm_num, by norm_num, f, hf1, hq, hmodel⟩
  by_cases hq' : p ∣ 2 ^ f + 1
  · exact ⟨9, by norm_num, by norm_num, by norm_num, f, hf1, hq', hmodel⟩
  exfalso
  have h1 : ¬ p ∣ (2 ^ f) ^ 2 - 1 := not_dvd_sq_sub_one hp Nat.one_le_two_pow hq hq'
  have hrank := h.localRank_eq_two_of_mulEquiv e
  have hgcd : ¬ p ∣ Nat.gcd 4 (2 ^ f + 1) := fun hd => hq' (hd.trans (Nat.gcd_dvd_right _ _))
  have h2 := localRank_statedProj_statedSU_le hK (by norm_num : 1 ≤ 4) hp hp2 hgcd
  have h3 := localRank_statedSU_four_le_one hK hp hp2 h1
  omega

theorem psu_five_row {G : Type} [Group G] [Finite G] {p : ℕ} {L A₀ F : Subgroup G}
    (h : Table123Generic p L A₀ F) {f : ℕ}
    (hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 5 2 f)
    (hlift : ∀ {K : Type} [Field K] [Finite K] [CharP K 2], UnitaryFieldData 2 f K →
      25 ∣ 2 ^ f + 1 → 3 ≤ localRank 5 (StatedProj (StatedSU 5 (2 ^ f) K))) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ 12 ∧ r ≠ 11 ∧ RowModel p L r := by
  have hmodel' := hmodel
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmodel'
  have hf1 : 1 ≤ f := hadm.2.1
  have hp := h.prime
  have hp5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := f * 2)
      (by rw [Fintype.card_eq_nat_card, hK, pow_mul])
  have hU : UnitaryFieldData 2 f K := unitaryFieldData_two hK hf1
  have hrank := h.localRank_eq_two_of_mulEquiv e
  by_cases hq : p ∣ 2 ^ f - 1
  · exact ⟨6, by norm_num, by norm_num, by norm_num, f, hf1, hq, hmodel⟩
  by_cases hq' : p ∣ 2 ^ f + 1
  · by_cases hp5' : p = 5
    · subst hp5'
      by_cases h25 : 25 ∣ 2 ^ f + 1
      · exfalso
        have := hlift hU h25
        omega
      · exact ⟨12, by norm_num, by norm_num, by norm_num, rfl, h.center_pPrime, f, hf1, hq', h25,
          hmodel⟩
    · exfalso
      have hn5 : ¬ p ∣ 5 := fun hd =>
        hp5' ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 hd)
      have h3 := le_localRank_statedSU_torus (k := 2) hU hp hq' (by norm_num) (Or.inr hn5)
      omega
  · exfalso
    have h1 : ¬ p ∣ (2 ^ f) ^ 2 - 1 := not_dvd_sq_sub_one hp Nat.one_le_two_pow hq hq'
    have hgcd : ¬ p ∣ Nat.gcd 5 (2 ^ f + 1) := fun hd => hq' (hd.trans (Nat.gcd_dvd_right _ _))
    have h2 := localRank_statedProj_statedSU_le hK (by norm_num : 1 ≤ 5) hp hp2 hgcd
    have h3 := localRank_statedSU_five_le_one hK hp hp2 h1
    omega

end CFSG.RankThree.PartOne
