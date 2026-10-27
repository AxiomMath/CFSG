module

public import CFSG.LocalAnalysis.StandardType.GGTBTorRel
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelA5Unitary
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelA5Linear

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTBTorRelA5_holds :
    GGTBTorRelA5 := by
  intro p hp hp2 lab hlab hrank htag
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hrank htag
  subst hrank
  have hn : 1 ≤ n := hlab.1
  rcases htag with ⟨ht, hpq⟩ | ⟨ht, hpq⟩
  ·
    subst ht
    have hpq' : ¬ p ∣ 2 ^ n - 1 := fun h =>
      not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 h hpq
    have hm : ggTorMpm p ⟨.A, 5, n⟩ = 2 ^ n + 1 := by
      unfold ggTorMpm
      dsimp only
      rw [if_neg hpq']
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
    refine ⟨K, i1, i2, hK, hQ', ?_⟩
    have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hK
    have key := RelA5.ggTorusTorW_relA5_linear (K := K) hp hp2 (by rw [hK]; exact hpq)
    rw [hm, ← hK]
    exact key
  ·
    subst ht
    have hm : ggTorMpm p ⟨.twA, 5, n⟩ = 2 ^ n - 1 := by
      unfold ggTorMpm
      dsimp only
      rw [if_pos hpq]
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
    refine ⟨K, i1, i2, hK, hQ', ?_⟩
    rw [hm]
    exact RelA5.ggTorusTorW_relA5_unitary hK hn hp hp2 hpq

end CFSG.StandardType
