module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

theorem uc22p2214_j1NotL2Sz : J1NotL2Sz := by
  intro X _ hX
  obtain ⟨e⟩ := hX
  have hcard : Nat.card X = 175560 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J1.card_J1
  haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · have h1 := uc22p22r_L2_card hn
    rw [hcard] at h1
    have hn2 : 2 ≤ n := (uc22p22g_isL2_psl hn).1
    have hpos : 1 ≤ (2 ^ n) ^ 2 - 1 := by
      have : 4 ≤ (2 ^ n) ^ 2 := by
        calc 4 = (2 ^ 1) ^ 2 := by norm_num
          _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) (by omega)) 2
      omega
    have hle : 2 ^ n ≤ 175560 := by
      rw [h1]
      exact Nat.le_mul_of_pos_right _ hpos
    have hn17 : n ≤ 17 := by
      by_contra h
      have : 2 ^ 18 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases n <;> norm_num at h1
  · have h3 := CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 hn
    rw [hcard] at h3
    exact h3 (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.UC22
