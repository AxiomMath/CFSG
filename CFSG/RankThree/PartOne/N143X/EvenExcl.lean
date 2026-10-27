module

public import CFSG.RankThree.PartOne.N143X.EvenSmall
public import CFSG.RankThree.PartOne.Census3.Interface
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.RankThree.PartTwo.Census.Classical.EvenBlocks
import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
import CFSG.RankThree.PartOne.KF.ClsSpWit
import CFSG.RankThree.PartOne.Census3.UnitarySixEight

public section

namespace CFSG.RankThree.PartOne.N143X

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Assembly.RankThreeEven
  CFSG.RankThree.PartOne.Census3 CFSG.RankThree.PartTwo.Census

theorem false_of_four_le_localRank {X Y : Type} [Group X] [Finite X] [Group Y] (e : X ≃* Y)
    (he : evenRank X ≤ 3) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h : ∀ [Finite Y], 4 ≤ localRank r Y) : False := by
  have h4 := four_le_twoLocalOddRank_of_mulEquiv e hr hr2 h
  rw [← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank] at h4
  omega

theorem false_of_four_le_carrier {X Y : Type} [Group X] [Finite X] [Group Y] (e : X ≃* Y)
    (he : evenRank X ≤ 3) (h4 : ∀ [Finite Y], 4 ≤ CFSG.twoLocalOddRank Y) : False := by
  have : Finite Y := Finite.of_equiv X e.toEquiv
  have h := h4
  rw [← twoLocalOddRank_eq_of_mulEquiv e,
    ← CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank] at h
  omega

theorem false_of_psl_large {X : Type} [Group X] [Finite X] {n f : ℕ}
    (hmod : StatedClassicalModel X .PSL n 2 f) (hbig : (6 ≤ n ∧ 2 ≤ f) ∨ 8 ≤ n)
    (he : evenRank X ≤ 3) : False := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hchar : CharP K 2 := charP_two_of_card hK
  let e' := e.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm
  rcases hbig with ⟨hn6, hf2⟩ | hn8
  · have hU : Nat.card Kˣ = 2 ^ f - 1 := by rw [Nat.card_units, hK]
    have h2f : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (show 2 ^ f - 1 ≠ 1 by omega)
    have hodd : (2 ^ f - 1) % 2 = 1 := by
      have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
      omega
    have hr2 : r ≠ 2 := by
      rintro rfl
      omega
    exact false_of_four_le_localRank e' he hr hr2
      (le_localRank_PSL_torus (m := 4) hr (by rw [hU]; exact hrd) (by omega) (by omega)
        (Or.inl (by omega)))
  · exact false_of_four_le_localRank e' he Nat.prime_three (by norm_num)
      (four_le_localRank_PSL_of_eight_le hn8)

theorem false_of_psu_large {X : Type} [Group X] [Finite X] {n f : ℕ}
    (hmod : StatedClassicalModel X .PSU n 2 f) (hbig : 7 ≤ n ∨ (n = 6 ∧ 2 ≤ f))
    (he : evenRank X ≤ 3) : False := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hf : 1 ≤ f := hadm.2.1
  have hK2 : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hchar : CharP K 2 := charP_two_of_card hK2
  have hu : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K :=
    ⟨Nat.prime_two, hf, hK2⟩
  rcases hbig with hn7 | ⟨rfl, hf2⟩
  · obtain ⟨s, hs, hs2, hsd⟩ := exists_odd_prime_dvd_two_pow_add_one hf
    refine false_of_four_le_localRank e he hs hs2 ?_
    have := le_localRank_statedSU_torus (k := 3) (n := n) hu hs hsd (by omega) (Or.inl (by omega))
    omega
  · by_cases hf3 : f = 3
    · subst hf3
      exact false_of_four_le_localRank e he Nat.prime_three (by norm_num)
        (localRankThreeU68 K (by rw [hK2]; norm_num))
    · obtain ⟨s, hs, hs5, hsd⟩ := exists_prime_five_le_dvd_two_pow_add_one hf2 hf3
      refine false_of_four_le_localRank e he hs (by omega) ?_
      have := le_localRank_statedSU_torus (k := 3) (n := 6) hu hs hsd (by norm_num)
        (Or.inr fun h6 => ?_)
      · omega
      · have hs6 := Nat.le_of_dvd (by norm_num) h6
        interval_cases s
        · exact absurd h6 (by norm_num)
        · exact absurd hs (by norm_num)

theorem false_of_psp_large {X : Type} [Group X] [Finite X] {n f : ℕ}
    (hmod : StatedClassicalModel X .PSp n 2 f) (hn : 5 ≤ n) (he : evenRank X ≤ 3) : False := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have hchar : CharP K 2 := charP_two_of_card hK
  refine false_of_four_le_localRank e he Nat.prime_three (by norm_num) ?_
  have := CFSG.RankThree.PartOne.KFU.le_localRank_three_statedSp_blocks (K := K) (m := m)
    (by omega)
  omega

end CFSG.RankThree.PartOne.N143X
