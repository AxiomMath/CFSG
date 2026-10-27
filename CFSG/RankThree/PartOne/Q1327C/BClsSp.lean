module

public import CFSG.RankThree.PartOne.Q1327C.BDefs
public import CFSG.RankThree.PartOne.KF.ClsPSp
public import CFSG.RankThree.PartOne.Q1327C.BBase
public import CFSG.RankThree.PartOne.Q1327C.BRows

public section

namespace CFSG.RankThree.PartOne.Q1327C

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU

variable {G : Type} [Group G] [Finite G] {p : ℕ} {X A₀ F : Subgroup G}

theorem bTag_PSp
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Q1327.T123Base p X A₀ F)
    (hLie : ∃ n f : ℕ, StatedLieAdmissible .PSp n 2 f ∧
      CFSG.Blueprint.LieModel (↥X ⧸ Subgroup.center ↥X) .PSp n 2 f) : BOutcome p X := by
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hcl : StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSp n 2 f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hcl' := hcl
  obtain ⟨hadm', K, hKf, hKfin, hK, ⟨e⟩⟩ := hcl'
  have hn2 : 2 ≤ n := hadm'.2.2.1
  have hf1 : 1 ≤ f := hadm'.2.1
  have hp := h.prime
  have hp5 := h.five_le
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := f)
      (by rw [Fintype.card_eq_nat_card]; exact hK)
  have hm : Models.LieModel (↥X ⧸ Subgroup.center ↥X) .PSp n 2 f := ⟨hadm', Or.inl hcl⟩
  have hdvd := T123Base.card_center_dvd_multiplier h hGA hm
  have hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center ↥X) := by
    intro r hr hr2 hrZ
    have h2 := (hrZ.trans hdvd).trans (card_multiplier_psp_dvd_two (n := n) hf1)
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2)
  have hrankP : 2 ≤ localRank p (StatedProj (StatedSp n K)) :=
    T123Base.two_le_localRank_of_mulEquiv h e
  have hle3 : ∀ r : ℕ, r.Prime → r ≠ 2 → localRank r (StatedProj (StatedSp n K)) ≤ 3 :=
    fun r hr hr2 => by
      rw [← CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hr]
      exact T123Base.localRank_quot_le_three h hZ hr hr2
  have hrankS : 2 ≤ localRank p ↥(StatedSp n K) := by
    rw [← localRank_statedProj_eq (K := K) (by omega) hp]
    exact hrankP
  have hp2 : p ≠ 2 := by omega
  rcases Nat.lt_or_ge n 5 with hn5 | hn5
  · have hn : n = 2 ∨ n = 3 ∨ n = 4 := by omega
    rcases hn with rfl | rfl | rfl
    · by_cases hpq : p ∣ 2 ^ f - 1
      · exact (false_of_row_rank_two h (r := 7) rfl
          (rowData_core_seven (T123Base.toCore h) ⟨f, hf1, hpq, hcl⟩)).elim
      · exfalso
        have := localRank_statedSp_two_le_one (K := K) hp hp2 (by rw [hK]; exact hpq)
        omega
    · by_cases hpq : p ∣ 2 ^ f - 1
      · exact BOutcome.of_Sp6 ⟨f, hf1, hpq, hcl⟩
      · by_cases hpq' : p ∣ 2 ^ f + 1
        · exact BOutcome.of_row10 ⟨f, hf1, hpq', hcl⟩
        · exfalso
          have := localRank_statedSp_three_le_one (K := K) hp hp2 (by rw [hK]; exact hpq)
            (by rw [hK]; exact hpq')
          omega
    · exfalso
      rcases Nat.lt_or_ge f 2 with hf | hf2
      · obtain rfl : f = 1 := by omega
        have hK2 : Nat.card K = 2 := by simpa using hK
        have := localRank_statedSp_four_le_one (K := K) hK2 hp hp5
        omega
      · obtain ⟨r, hr, hr2, -, hrd⟩ := exists_odd_prime_dvd_two_pow_sub_one_ne_five hf2
        have hrK : r ∣ Nat.card Kˣ := by rw [Nat.card_units, hK]; exact hrd
        have h4 := le_localRank_statedSp_torus (K := K) hr hr2 hrK (by norm_num : 1 ≤ 4)
        have h3 := hle3 r hr hr2
        omega
  · exfalso
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h1 := le_localRank_three_statedSp_blocks (K := K) (m := m) (by omega)
    have h2 := hle3 3 Nat.prime_three (by norm_num)
    omega

end CFSG.RankThree.PartOne.Q1327C
