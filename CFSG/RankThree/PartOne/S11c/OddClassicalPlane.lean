module

public import CFSG.RankThree.PartOne.S11c.PlaneHigherUnitary
public import CFSG.RankThree.PartOne.S11c.PlaneSp
public import CFSG.RankThree.PartOne.S11c.ClassicalPSL2
public import CFSG.RankThree.PartOne.S11c.PlaneOrthogonal
public import CFSG.RankThree.PartOne.S11c.DegreeFourPlane
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.RankThree.LocalRank.SelectorCases

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (localRank)

theorem degreeFourPlane : DegreeFourPlane :=
  fun _ _ h2 _ hn _ _ _ hQ _ hp hp3 hdet hel hcard hEQ =>
    odd_characteristic_degree_four_special_linear_plane_centralizes_two_subgroup h2 hn hQ hp hp3
      hdet hel hcard hEQ

theorem degreeSixPrimes : DegreeSixPrimes :=
  fun _ _ h2 _ hn _ _ _ hQ _ hp hp5 _ hP hPQ =>
    odd_characteristic_degree_six_primes_above_five_centralize_two_subgroups h2 hn hQ hp hp5 hP
      hPQ

theorem actualCoverOddClassicalPlaneCentralization :
    ActualCoverOddClassicalPlaneCentralization := by
  intro H _ _ he X hXqs t n ℓ f ht hℓ hℓ2 hf hmod p E U hplane
  have hloc : localRank ℓ H ≤ 3 := by
    rcases Nat.eq_zero_or_pos (localRank ℓ H) with h0 | hpos
    · omega
    · exact (CFSG.RankThree.Theta.localRank_le_twoLocalOddRank hℓ hℓ2
        (CFSG.RankThree.LocalRank.prime_dvd_card_of_localRank_pos hℓ hpos)).trans he
  simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  ·
    obtain ⟨-, -, hn, -⟩ := hmod.1
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · have hn2 : n = 2 := by omega
      subst hn2
      obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmod.2
      have : CharP K ℓ :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
      exact planeCentralizes_psl_two (by rw [ringChar.eq K ℓ]; exact hℓ2) e hplane
    · exact planeCentralizes_psl_higher hXqs h3 hℓ hℓ2 hmod hloc hplane degreeFourPlane
        degreeSixPrimes
  ·
    obtain ⟨-, -, hn, -⟩ := hmod.1
    exact planeCentralizes_psu_higher hXqs hn hℓ hℓ2 hmod hloc hplane degreeFourPlane
      degreeSixPrimes
  ·
    exact planeCentralizes_psp hXqs hℓ hℓ2 hmod hloc hplane degreeFourPlane
  · exact (orthogonal_model_absurd (Or.inl rfl) hℓ hℓ2 hmod hloc).elim
  · exact (orthogonal_model_absurd (Or.inr (Or.inl rfl)) hℓ hℓ2 hmod hloc).elim
  · exact (orthogonal_model_absurd (Or.inr (Or.inr rfl)) hℓ hℓ2 hmod hloc).elim

end CFSG.RankThree.PartOne
