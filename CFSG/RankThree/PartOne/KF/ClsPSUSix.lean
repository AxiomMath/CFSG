module

public import CFSG.RankThree.PartOne.KF.ClsSUUpper
public import CFSG.RankThree.PartOne.KF.ClsCenter
public import CFSG.RankThree.PartTwo.Census.Classical.EvenHyperbolic
public import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.KFU CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.Census

namespace KFU

variable {K : Type} [Field K] [Finite K]

theorem localRank_le_one_of_not_sq_dvd {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ^ 2 ∣ Nat.card G) : localRank p G ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨U, -, -, E, -, -, hEc⟩ := exists_elemAbelian_of_le_localRank hp (by omega : 1 ≤ 2) hlt
  exact h (hEc ▸ Subgroup.card_subgroup_dvd_card E)

omit [Finite K] in
theorem card_statedSU_six_one [CharP K 2] (hK : Nat.card K = (2 ^ 1) ^ 2) :
    Nat.card (StatedSU 6 (2 ^ 1) K) = 2 ^ 15 * 841995 := by
  have h := card_statedSU_eq (unitaryFieldData_two hK (by norm_num)) (n := 6) (by norm_num)
  have hprod : ∏ i ∈ Finset.Icc 2 6, (((2 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) = 841995 := by decide
  rw [hprod] at h
  have : (Nat.card (StatedSU 6 (2 ^ 1) K) : ℤ) = 2 ^ 15 * 841995 := by
    rw [h]
    norm_num
  exact_mod_cast this

omit [Finite K] in
theorem card_statedSU_six_three [CharP K 2] (hK : Nat.card K = (2 ^ 3) ^ 2) :
    Nat.card (StatedSU 6 (2 ^ 3) K) = 8 ^ 15 * (63 * 513 * 4095 * 32769 * 262143) := by
  have h := card_statedSU_eq (unitaryFieldData_two hK (by norm_num)) (n := 6) (by norm_num)
  have hprod : ∏ i ∈ Finset.Icc 2 6, (((2 ^ 3 : ℕ) : ℤ) ^ i - (-1) ^ i) =
      63 * 513 * 4095 * 32769 * 262143 := by decide
  rw [hprod] at h
  have : (Nat.card (StatedSU 6 (2 ^ 3) K) : ℤ) = 8 ^ 15 * (63 * 513 * 4095 * 32769 * 262143) := by
    rw [h]
    norm_num
  exact_mod_cast this

theorem localRank_statedSU_six_one_le_one [CharP K 2] (hK : Nat.card K = (2 ^ 1) ^ 2) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) : localRank p ↥(StatedSU 6 (2 ^ 1) K) ≤ 1 := by
  have hp2 : p ≠ 2 := by omega
  by_cases h15 : p ∣ (2 ^ 1) ^ 4 - 1
  · have h15' : p ∣ 3 * 5 := by simpa using h15
    rcases (Nat.Prime.dvd_mul hp).1 h15' with h3 | h5
    · have := Nat.le_of_dvd (by norm_num) h3
      omega
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h5
      refine localRank_le_one_of_not_sq_dvd Nat.prime_five ?_
      rw [card_statedSU_six_one hK]
      decide
  · refine localRank_statedSU_six_le_one hK hp hp2 ?_ h15
    intro h3
    have h3' : p ∣ 3 := by simpa using h3
    have := Nat.le_of_dvd (by norm_num) h3'
    omega

theorem localRank_statedSU_six_three_le_one [CharP K 2] (hK : Nat.card K = (2 ^ 3) ^ 2) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hp7 : p ≠ 7) : localRank p ↥(StatedSU 6 (2 ^ 3) K) ≤ 1 := by
  have hp2 : p ≠ 2 := by omega
  have h63 : ¬ p ∣ (2 ^ 3) ^ 2 - 1 := by
    intro h
    have h' : p ∣ 3 * 3 * 7 := by simpa using h
    rcases (Nat.Prime.dvd_mul hp).1 h' with h1 | h7
    · rcases (Nat.Prime.dvd_mul hp).1 h1 with h3 | h3
      · have := Nat.le_of_dvd (by norm_num) h3
        omega
      · have := Nat.le_of_dvd (by norm_num) h3
        omega
    · exact hp7 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h7)
  by_cases h4095 : p ∣ (2 ^ 3) ^ 4 - 1
  · have h' : p ∣ (3 * 3 * 7) * (5 * 13) := by simpa using h4095
    rcases (Nat.Prime.dvd_mul hp).1 h' with h1 | h2
    · exact absurd (by simpa using h1) h63
    · rcases (Nat.Prime.dvd_mul hp).1 h2 with h5 | h13
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h5
        refine localRank_le_one_of_not_sq_dvd Nat.prime_five ?_
        rw [card_statedSU_six_three hK]
        decide
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 13)).1 h13
        refine localRank_le_one_of_not_sq_dvd (by norm_num) ?_
        rw [card_statedSU_six_three hK]
        decide
  · exact localRank_statedSU_six_le_one hK hp hp2 h63 h4095

end KFU

namespace Table123Generic

variable {G : Type} [Group G] [Finite G] {p : ℕ} {L A₀ F : Subgroup G}
  (h : Table123Generic p L A₀ F)

include h in
theorem localRank_quot_le_three_of {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrZ : ¬ r ∣ Nat.card (Subgroup.center ↥L)) :
    localRank r (↥L ⧸ Subgroup.center ↥L) ≤ 3 := by
  have h1 := CFSG.RankThree.Classical2.localRank_quotient_le hr hr2 (Subgroup.center ↥L) hrZ
  exact h1.trans ((CFSG.RankThree.OddKernel.localRank_le_evenRank hr hr2).trans h.evenRank_le)

end Table123Generic

open KFU in
theorem psu_six_false {G : Type} [Group G] [Finite G] {p : ℕ} {L A₀ F : Subgroup G}
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Table123Generic p L A₀ F) {f : ℕ}
    (hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 6 2 f) : False := by
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
  rcases (show f = 1 ∨ f = 3 ∨ (2 ≤ f ∧ f ≠ 3) by omega) with rfl | rfl | ⟨hf2, hf3⟩
  ·
    have hrank := h.localRank_eq_two_of_mulEquiv e
    have hgcd : ¬ p ∣ Nat.gcd 6 (2 ^ 1 + 1) := by
      intro hd
      have : p ∣ 3 := by simpa using hd
      have := Nat.le_of_dvd (by norm_num) this
      omega
    have h1 := localRank_statedProj_statedSU_le hK (by norm_num : 1 ≤ 6) hp hp2 hgcd
    have h2 := localRank_statedSU_six_one_le_one hK hp hp5
    omega
  ·
    have hrank := h.localRank_eq_two_of_mulEquiv e
    have hgcd : ¬ p ∣ Nat.gcd 6 (2 ^ 3 + 1) := by
      intro hd
      have : p ∣ 3 := by simpa using hd
      have := Nat.le_of_dvd (by norm_num) this
      omega
    by_cases hp7 : p = 7
    · subst hp7
      have h3 : 3 ≤ localRank 7 (StatedProj (StatedSU 6 (2 ^ 3) K)) :=
        three_le_localRank_statedSU_six_eight hU
      omega
    · have h1 := localRank_statedProj_statedSU_le hK (by norm_num : 1 ≤ 6) hp hp2 hgcd
      have h2 := localRank_statedSU_six_three_le_one hK hp hp5 hp7
      omega
  ·
    obtain ⟨s, hs, hs5, hsd⟩ := exists_prime_five_le_dvd_two_pow_add_one hf2 hf3
    have hs2 : s ≠ 2 := by omega
    have hn6 : ¬ s ∣ 6 := by
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      interval_cases s <;> first | omega | exact absurd hs (by norm_num)
    have h4 := le_localRank_statedSU_torus (k := 3) hU hs hsd (by norm_num) (Or.inr hn6)
    have hadm' : StatedLieAdmissible .PSU 6 2 f := hadm
    have hm : Models.LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 6 2 f := ⟨hadm', Or.inl hmodel⟩
    have hdvd := h.card_center_dvd_multiplier hGA hm
    have hgen : Blueprint.Multiplier.genericOrders .PSU 6 2 f = (Nat.gcd 6 (2 ^ f + 1), 1) := rfl
    have hexc : Blueprint.Multiplier.exceptionalOrders .PSU 6 2 f = (1, 1) := by
      unfold Blueprint.Multiplier.exceptionalOrders
      split <;> simp_all
    have hcard : Nat.card (Blueprint.Multiplier.generic .PSU 6 2 f ×
        Blueprint.Multiplier.exceptional .PSU 6 2 f) = Nat.gcd 6 (2 ^ f + 1) := by
      unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
      rw [hgen, hexc]
      simp [Nat.card_prod, Nat.card_congr Multiplicative.toAdd]
    have hsZ : ¬ s ∣ Nat.card (Subgroup.center ↥L) := by
      intro hsz
      have := ((hsz.trans hdvd).trans (hcard ▸ dvd_refl _)).trans (Nat.gcd_dvd_left 6 (2 ^ f + 1))
      exact hn6 this
    have h3 := h.localRank_quot_le_three_of hs hs2 hsZ
    rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hs] at h3
    omega

end CFSG.RankThree.PartOne
