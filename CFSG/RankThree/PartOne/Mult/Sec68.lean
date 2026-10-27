module

public import CFSG.RankThree.PartOne.Mult.Alternating
public import CFSG.RankThree.PartOne.Mult.Exceptional
public import CFSG.RankThree.PartOne.Mult.Sporadic

public section

namespace CFSG.RankThree.PartOne.Mult

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier CFSG.RankThree.PartOne

theorem sec6Eight_of_residual
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hres : SporadicResidualKernels) : Sec6EightMultipliers := by
  intro H _ _ he K p hp hp3 hK hcat hpZ
  have : Group.IsPerfect ↥K := hK.1
  rcases hcat with ⟨q, hq, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | hcl | hex | hsp
  · exfalso
    obtain ⟨a, b, hab⟩ := hK.2.2
    exact hab (e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _))
  · exact absurd hpZ (alternating_center_small_primes hm e hp hp3)
  · obtain ⟨t, n, ℓ, f, hmod⟩ := hcl
    have hdvd := card_center_dvd_of_model hGA hK hmod
    rcases prime_dvd_table hp hp3 (hpZ.trans hdvd) with ⟨rfl, hpn, hpq⟩ | ⟨rfl, hpn, hpq⟩
    · exact (sec68_psl he hp hp3 hpZ hmod hpn hpq).elim
    · obtain ⟨rfl, rfl, rfl⟩ := sec68_psu he hp hp3 hpZ hmod hpn hpq
      have hf : 1 ≤ f := hmod.1.2.1
      have hord : (genericOrders .PSU 5 2 f).1 * (genericOrders .PSU 5 2 f).2 *
          ((exceptionalOrders .PSU 5 2 f).1 * (exceptionalOrders .PSU 5 2 f).2) = 5 := by
        have h1 : genericOrders .PSU 5 2 f = (Nat.gcd 5 (2 ^ f + 1), 1) := rfl
        have h2 : exceptionalOrders .PSU 5 2 f = (1, 1) := by
          unfold exceptionalOrders
          simp
        rw [h1, h2, Nat.gcd_eq_left hpq]
        norm_num
      rw [hord] at hdvd
      exact ⟨rfl, Nat.dvd_antisymm hdvd hpZ, f, hf, hmod⟩
  · exact absurd hpZ (exceptionalCenterSmallPrimes_of_griess hGA ↥K hK hex p hp hp3)
  · exact absurd hpZ (sporadicCenterSmallPrimes_of_residual hres ↥K hK hsp p hp hp3)

end CFSG.RankThree.PartOne.Mult
