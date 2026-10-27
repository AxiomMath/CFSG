module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4SmallContracts
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmall

public section

namespace CFSG.StandardType.GGInnerD4SmallParts

open CFSG CFSG.Assembly CFSG.StandardType

private theorem ltrsm2_three_dvd_two_pow_odd_add_one (k : ℕ) : 3 ∣ 2 ^ (2 * k + 1) + 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hpow : 2 ^ (2 * (k + 1) + 1) = 4 * 2 ^ (2 * k + 1) := by
      rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, pow_add]
      ring
    rw [hpow]
    obtain ⟨m, hm⟩ := ih
    exact ⟨4 * m - 1, by omega⟩

theorem suzukiOrderInput_holds :
    S2MathAs51600Small.SuzukiOrderInput := by
  intro lab hlab ht
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab ⊢
  subst ht
  obtain ⟨k, hk⟩ := hlab.2.2.1
  have hk' : n = 2 * k + 1 := hk
  have hna : 2 * ((n - 1) / 2) + 1 = n := by omega
  have hpq : 3 ∣ 2 ^ (2 * ((n - 1) / 2) + 1) + 1 := by
    rw [hna, hk']
    exact ltrsm2_three_dvd_two_pow_odd_add_one k
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq'⟩ := hQ
  refine ⟨K, i1, i2, hK, hq', ?_⟩
  have hnot : ¬ 3 ∣ Nat.card (LargeEvenSzGroup ((n - 1) / 2) K) := by
    rw [largeEvenSzGroup_eq ((n - 1) / 2) K, CFSG.LieType.Ree.suzuki_order hK]
    exact CFSG.StandardType.TableBExc.not_dvd_card_suzuki (p := 3)
      (n := 2 * ((n - 1) / 2) + 1) Nat.prime_three (by norm_num) hpq
  have hdvd : Nat.card (LargeEvenCenterQuot (LargeEvenSzGroup ((n - 1) / 2) K)) ∣
      Nat.card (LargeEvenSzGroup ((n - 1) / 2) K) :=
    Subgroup.card_quotient_dvd_card (Subgroup.center ↥(LargeEvenSzGroup ((n - 1) / 2) K))
  intro h
  exact hnot (dvd_trans h hdvd)

end CFSG.StandardType.GGInnerD4SmallParts

end
