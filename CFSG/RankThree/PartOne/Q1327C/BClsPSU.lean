module

public import CFSG.RankThree.PartOne.Q1327C.BDefs
public import CFSG.RankThree.PartOne.KF.ClsPSUBig
public import CFSG.RankThree.PartOne.KF.ClsPSUSix
public import CFSG.RankThree.PartOne.KF.ClsSU3
public import CFSG.RankThree.PartOne.KF.ClsSpUpper
public import CFSG.RankThree.PartOne.Q1327C.BBase
public import CFSG.RankThree.PartOne.Q1327C.BRows

public section

namespace CFSG.RankThree.PartOne.Q1327C

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.Census

variable {G : Type} [Group G] [Finite G] {p : ℕ} {X A₀ F : Subgroup G}

theorem psu_three_false_B (h : Q1327.T123Base p X A₀ F) {f : ℕ}
    (hmodel : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSU 3 2 f) : False := by
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmodel
  have hp := h.prime
  have hp5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := f * 2)
      (by rw [Fintype.card_eq_nat_card, hK, pow_mul])
  have hrank := T123Base.two_le_localRank_of_mulEquiv h e
  have hgcd : ¬ p ∣ Nat.gcd 3 (2 ^ f + 1) := fun hd => by
    have := Nat.le_of_dvd (by norm_num) (hd.trans (Nat.gcd_dvd_left _ _))
    omega
  have h2 := localRank_statedProj_statedSU_le hK (by norm_num : 1 ≤ 3) hp hp2 hgcd
  have h3 := localRank_statedSU_three_le_one hK hp hp2
  omega

theorem psu_four_B (h : Q1327.T123Base p X A₀ F) {f : ℕ}
    (hmodel : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSU 4 2 f) :
    p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1 := by
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
  · exact Or.inl hq
  by_cases hq' : p ∣ 2 ^ f + 1
  · exact Or.inr hq'
  exfalso
  have h1 : ¬ p ∣ (2 ^ f) ^ 2 - 1 := not_dvd_sq_sub_one hp Nat.one_le_two_pow hq hq'
  have hrank := T123Base.two_le_localRank_of_mulEquiv h e
  have hgcd : ¬ p ∣ Nat.gcd 4 (2 ^ f + 1) := fun hd => hq' (hd.trans (Nat.gcd_dvd_right _ _))
  have h2 := localRank_statedProj_statedSU_le hK (by norm_num : 1 ≤ 4) hp hp2 hgcd
  have h3 := localRank_statedSU_four_le_one hK hp hp2 h1
  omega

theorem psu_five_B (h : Q1327.T123Base p X A₀ F) {f : ℕ}
    (hmodel : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSU 5 2 f) :
    p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1 := by
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
  have hrank := T123Base.two_le_localRank_of_mulEquiv h e
  by_cases hq : p ∣ 2 ^ f - 1
  · exact Or.inl hq
  by_cases hq' : p ∣ 2 ^ f + 1
  · exact Or.inr hq'
  exfalso
  have h1 : ¬ p ∣ (2 ^ f) ^ 2 - 1 := not_dvd_sq_sub_one hp Nat.one_le_two_pow hq hq'
  have hgcd : ¬ p ∣ Nat.gcd 5 (2 ^ f + 1) := fun hd => hq' (hd.trans (Nat.gcd_dvd_right _ _))
  have h2 := localRank_statedProj_statedSU_le hK (by norm_num : 1 ≤ 5) hp hp2 hgcd
  have h3 := localRank_statedSU_five_le_one hK hp hp2 h1
  omega

theorem psu_six_false_B
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Q1327.T123Base p X A₀ F) (h7 : p ≠ 7) {f : ℕ}
    (hmodel : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSU 6 2 f) : False := by
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
  · have hrank := T123Base.two_le_localRank_of_mulEquiv h e
    have hgcd : ¬ p ∣ Nat.gcd 6 (2 ^ 1 + 1) := by
      intro hd
      have : p ∣ 3 := by simpa using hd
      have := Nat.le_of_dvd (by norm_num) this
      omega
    have h1 := localRank_statedProj_statedSU_le hK (by norm_num : 1 ≤ 6) hp hp2 hgcd
    have h2 := localRank_statedSU_six_one_le_one hK hp hp5
    omega
  · have hrank := T123Base.two_le_localRank_of_mulEquiv h e
    have hgcd : ¬ p ∣ Nat.gcd 6 (2 ^ 3 + 1) := by
      intro hd
      have : p ∣ 3 := by simpa using hd
      have := Nat.le_of_dvd (by norm_num) this
      omega
    have h1 := localRank_statedProj_statedSU_le hK (by norm_num : 1 ≤ 6) hp hp2 hgcd
    have h2 := localRank_statedSU_six_three_le_one hK hp hp5 h7
    omega
  · obtain ⟨s, hs, hs5, hsd⟩ := exists_prime_five_le_dvd_two_pow_add_one hf2 hf3
    have hs2 : s ≠ 2 := by omega
    have hn6 : ¬ s ∣ 6 := by
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      interval_cases s <;> first | omega | exact absurd hs (by norm_num)
    have h4 := le_localRank_statedSU_torus (k := 3) hU hs hsd (by norm_num) (Or.inr hn6)
    have hadm' : StatedLieAdmissible .PSU 6 2 f := hadm
    have hm : Models.LieModel (↥X ⧸ Subgroup.center ↥X) .PSU 6 2 f := ⟨hadm', Or.inl hmodel⟩
    have hdvd := T123Base.card_center_dvd_multiplier h hGA hm
    have hgen : Blueprint.Multiplier.genericOrders .PSU 6 2 f = (Nat.gcd 6 (2 ^ f + 1), 1) := rfl
    have hexc : Blueprint.Multiplier.exceptionalOrders .PSU 6 2 f = (1, 1) := by
      unfold Blueprint.Multiplier.exceptionalOrders
      split <;> simp_all
    have hcard : Nat.card (Blueprint.Multiplier.generic .PSU 6 2 f ×
        Blueprint.Multiplier.exceptional .PSU 6 2 f) = Nat.gcd 6 (2 ^ f + 1) := by
      unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
      rw [hgen, hexc]
      simp [Nat.card_prod, Nat.card_congr Multiplicative.toAdd]
    have hsZ : ¬ s ∣ Nat.card (Subgroup.center ↥X) := by
      intro hsz
      have := ((hsz.trans hdvd).trans (hcard ▸ dvd_refl _)).trans (Nat.gcd_dvd_left 6 (2 ^ f + 1))
      exact hn6 this
    have h3 := T123Base.localRank_quot_le_three_of h hs hs2 hsZ
    rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hs] at h3
    omega

theorem psu_large_false_B
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Q1327.T123Base p X A₀ F) {n f : ℕ} (hn : 7 ≤ n)
    (hmodel : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSU n 2 f) : False := by
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmodel
  have hf1 : 1 ≤ f := hadm.2.1
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥X)) := T123Base.coprime_center h
  have hq := isCentralPQuot_center e hcop
  have hLp : Group.IsPerfect ↥X := h.quasisimple.1
  obtain ⟨ρ, hρs, hρk⟩ := exists_cover_psu hGA hn hf1 hK hLp _ hq.surjective hq.central
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := f * 2)
      (by rw [Fintype.card_eq_nat_card, hK, pow_mul])
  have hU : UnitaryFieldData 2 f K := unitaryFieldData_two hK hf1
  obtain ⟨r, hr, hr2, hrq⟩ := CFSG.RankThree.PartTwo.Census.exists_odd_prime_dvd_two_pow_add_one hf1
  have h4 := CFSG.RankThree.PartOne.KFU.le_localRank_of_surjective_statedSU_torus (k := 3) hU hr
    hrq (by omega) (Or.inl (by omega)) ρ hρs hρk
  have h3 := (CFSG.RankThree.OddKernel.localRank_le_evenRank hr hr2).trans h.evenRank_le
  omega

theorem bTag_PSU
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Q1327.T123Base p X A₀ F) (h7 : p ≠ 7)
    (hLie : ∃ n f : ℕ, StatedLieAdmissible .PSU n 2 f ∧
      CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) .PSU n 2 f) : BOutcome p X := by
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hcl : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSU n 2 f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hf1 : 1 ≤ f := hadm.2.1
  rcases (show n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ 7 ≤ n by omega) with rfl | rfl | rfl | rfl | hn7
  · exact (psu_three_false_B h hcl).elim
  · rcases psu_four_B h hcl with hq | hq
    · exact (false_of_row_rank_two h (r := 5) rfl
        (rowData_core_five (T123Base.toCore h) ⟨f, hf1, hq, hcl⟩)).elim
    · exact BOutcome.of_row9 ⟨f, hf1, hq, hcl⟩
  · rcases psu_five_B h hcl with hq | hq
    · exact (false_of_row_rank_two h (r := 6) rfl
        (rowData_core_six (T123Base.toCore h) ⟨f, hf1, hq, hcl⟩)).elim
    · by_cases h5 : p = 5 ∧ ¬ 25 ∣ 2 ^ f + 1
      · obtain ⟨rfl, h25⟩ := h5
        exact BOutcome.of_row12 ⟨rfl, h.center_pPrime, f, hf1, hq, h25, hcl⟩
      · refine BOutcome.of_U5 ⟨f, hf1, hq, ?_, hcl⟩
        by_cases hp5 : p = 5
        · exact Or.inr (by
            by_contra h25
            exact h5 ⟨hp5, h25⟩)
        · exact Or.inl hp5
  · exact (psu_six_false_B hGA h h7 hcl).elim
  · exact (psu_large_false_B hGA h hn7 hcl).elim

end CFSG.RankThree.PartOne.Q1327C
