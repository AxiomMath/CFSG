module

public import CFSG.RankThree.PartOne.KC.LinearNoninnerPlaneGeneral
public import CFSG.RankThree.PartOne.KC.LinearPrimeFieldActorSolvableCore
public import CFSG.RankThree.PartOne.KC.LinearCommutatorNodes

public section

namespace CFSG.RankThree.PartOne

open CFSG.LocalAnalysis.ComponentInitial

theorem linear_below_prime_noninner_plane_local_core_product_odd :
    LinearBelowPrimeNoninnerPlaneLocalCoreOdd := by
  intro p ℓ f n K _ hp hp3 hℓ hℓp hf hn hnp hK B hB A hAB hAel hAcard hAH
  have : IsElementaryAbelian p A := hAel
  have hp2 : p ≠ 2 := by omega
  have hCharP : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have hnpc : Nat.Coprime n p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_of_pos_of_lt (by omega) hnp)).symm
  have hcop : Nat.Coprime p (Nat.gcd n (Nat.card K - 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left n _) hnpc.symm
  obtain ⟨h1, h2, -, -, h5, h6, h7⟩ := KCLinPlane.noninner_plane_data hp hp2 hℓ hℓp hf hn hK hcop
    B A hAB hAcard hAH
    (fun a haB haE haD hord => higher_linear_prime_field_actor_solvable_core_trivial hℓ hp
      hℓp.symm hf hn hnpc hK B hB haB haE haD hord)
    (fun hq t ht htp A' hA' hA'p => linear_below_prime_inner_actor_local_core_commutators_odd hp
      hp3 hℓ hℓp hf hn hnp hK hq B hB ht htp A' hA' hA'p)
  exact ⟨h1, h2, h5, h6, h7⟩

end CFSG.RankThree.PartOne
