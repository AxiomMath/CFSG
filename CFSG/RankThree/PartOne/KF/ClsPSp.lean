module

public import CFSG.RankThree.PartOne.KF.ClassifyTags
public import CFSG.RankThree.PartOne.KF.ClsCenter
public import CFSG.RankThree.PartOne.KF.ClsSpUpper
public import CFSG.RankThree.PartOne.KF.ClsSpWit
public import CFSG.RankThree.PartOne.KF.ClsPSLBig
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.KFU

namespace KFU

theorem card_multiplier_psp_dvd_two {n f : ℕ} (hf : 1 ≤ f) :
    Nat.card (Blueprint.Multiplier.generic .PSp n 2 f ×
      Blueprint.Multiplier.exceptional .PSp n 2 f) ∣ 2 := by
  have hgen : Blueprint.Multiplier.genericOrders .PSp n 2 f = (Nat.gcd 2 (2 ^ f - 1), 1) := rfl
  have hodd : Nat.gcd 2 (2 ^ f - 1) = 1 := by
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have hm : (2 ^ f - 1) % 2 = 1 := by omega
    rw [Nat.gcd_rec, hm]
    rfl
  have hexc : Blueprint.Multiplier.exceptionalOrders .PSp n 2 f = (2, 1) ∨
      Blueprint.Multiplier.exceptionalOrders .PSp n 2 f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hodd]
  rcases hexc with h | h <;> rw [h] <;> simp

end KFU

theorem kf123ClassifyTag_PSp
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF123ClassifyTag .PSp := by
  intro G _ _ p L A₀ F h hLie
  obtain ⟨n, f, hadm, hmodel⟩ := hLie
  have hcl : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSp n 2 f := by
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
  have hm : Models.LieModel (↥L ⧸ Subgroup.center ↥L) .PSp n 2 f := ⟨hadm', Or.inl hcl⟩
  have hdvd := h.card_center_dvd_multiplier hGA hm
  have hZ : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card (Subgroup.center ↥L) := by
    intro r hr hr2 hrZ
    have h2 := (hrZ.trans hdvd).trans (card_multiplier_psp_dvd_two (n := n) hf1)
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2)
  have hrankP : localRank p (StatedProj (StatedSp n K)) = 2 := h.localRank_eq_two_of_mulEquiv e
  have hle3 : ∀ r : ℕ, r.Prime → r ≠ 2 → localRank r (StatedProj (StatedSp n K)) ≤ 3 :=
    fun r hr hr2 => by
      rw [← CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hr]
      exact h.localRank_quot_le_three hZ hr hr2
  have hrankS : localRank p ↥(StatedSp n K) = 2 := by
    rw [← localRank_statedProj_eq (K := K) (by omega) hp]
    exact hrankP
  have hp2 : p ≠ 2 := by omega
  rcases Nat.lt_or_ge n 5 with hn5 | hn5
  · have hn : n = 2 ∨ n = 3 ∨ n = 4 := by omega
    rcases hn with rfl | rfl | rfl
    ·
      by_cases hpq : p ∣ 2 ^ f - 1
      · exact ⟨7, by norm_num, by norm_num, by norm_num, f, hf1, hpq, hcl⟩
      · exfalso
        have := localRank_statedSp_two_le_one (K := K) hp hp2 (by rw [hK]; exact hpq)
        omega
    ·
      by_cases hpq : p ∣ 2 ^ f - 1
      · exfalso
        have hrK : p ∣ Nat.card Kˣ := by rw [Nat.card_units, hK]; exact hpq
        have h3 := le_localRank_statedSp_torus (K := K) hp hp2 hrK (by norm_num : 1 ≤ 3)
        omega
      · by_cases hpq' : p ∣ 2 ^ f + 1
        · exact ⟨10, by norm_num, by norm_num, by norm_num, f, hf1, hpq', hcl⟩
        · exfalso
          have := localRank_statedSp_three_le_one (K := K) hp hp2 (by rw [hK]; exact hpq)
            (by rw [hK]; exact hpq')
          omega
    ·
      exfalso
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
  ·
    exfalso
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h1 := le_localRank_three_statedSp_blocks (K := K) (m := m) (by omega)
    have h2 := hle3 3 Nat.prime_three (by norm_num)
    omega

end CFSG.RankThree.PartOne
