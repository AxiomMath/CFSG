module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSuzukiOddCore
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem false_of_twistedB2 {T : Type} [Group T] [Finite T]
    {p n f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hmodel : LieModel T .twistedB2 n 2 (p * f))
    {x y : T} (hxp : x ^ p = 1) (hx1 : x ≠ 1) (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1)
    (hxy : x * y = y * x) : False := by
  rcases hmodel with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, hS⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  obtain ⟨-, a, ha, K, _, _, hfa, hKcard, ⟨e⟩⟩ := hS
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hKcard
  have : Fact p.Prime := ⟨hp⟩
  have hyo : orderOf (e y) = 2 :=
    orderOf_eq_prime (by rw [← map_pow, hy2, map_one])
      (fun h1 => hy1 (e.injective (h1.trans (map_one e).symm)))
  obtain ⟨S, hS⟩ :=
    ComponentClassification.UnbalancedGS.SuzukiOddCore.suzuki_involution_centralizer_sylow hK
      (e y) hyo
  have hxS : e x ∈ (S : Subgroup (suzukiGroup a K)) := by
    rw [hS]
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by rw [← map_mul, ← map_mul, hxy])
  have hxord : orderOf (e x) = p :=
    orderOf_eq_prime (by rw [← map_pow, hxp, map_one])
      (fun h1 => hx1 (e.injective (h1.trans (map_one e).symm)))
  have hpS : IsPGroup 2 (S : Subgroup (suzukiGroup a K)) := S.isPGroup'
  obtain ⟨k, hk⟩ := hpS ⟨e x, hxS⟩
  have hdvd : p ∣ 2 ^ k := by
    have h1 : orderOf (⟨e x, hxS⟩ : (S : Subgroup (suzukiGroup a K))) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one hk
    rwa [Subgroup.orderOf_mk, hxord] at h1
  have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd)
  omega

end CFSG.RankThree.PartOne
