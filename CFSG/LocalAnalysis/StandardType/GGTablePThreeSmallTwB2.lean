module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSmallDefs
import CFSG.LocalAnalysis.StandardType.GGTableBTransport

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

private theorem three_dvd_two_pow_add_one_of_odd {n : ℕ} (hn : Odd n) : 3 ∣ 2 ^ n + 1 := by
  rw [← ZMod.natCast_eq_zero_iff (2 ^ n + 1) 3]
  push_cast
  have h2 : (2 : ZMod 3) = -1 := by decide
  have hneg : ((-1 : ZMod 3) ^ n) = -1 := hn.neg_one_pow
  rw [h2, hneg]
  decide

section Certs

theorem svRankTwB2_holds :
    SVRank (fun t => t = .twB2) := by
  intro lab hlab ht
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab ⊢
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq'⟩ := hQ
  refine ⟨K, i1, i2, hK, hq', ?_⟩
  intro _ _ B hB hBI
  haveI : Finite (LargeEvenSzGroup ((n - 1) / 2) K) := Subtype.finite
  haveI : Finite (LargeEvenCenterQuot (LargeEvenSzGroup ((n - 1) / 2) K)) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  haveI := TableBSymp.finite_mulAut (R := LargeEvenCenterQuot (LargeEvenSzGroup ((n - 1) / 2) K))
  obtain ⟨k, hk⟩ := hlab.2.2.1
  have hk' : n = 2 * k + 1 := hk
  have hna : 2 * ((n - 1) / 2) + 1 = n := by omega
  have hBr : B ≤ (MulAut.conj : LargeEvenCenterQuot (LargeEvenSzGroup ((n - 1) / 2) K) →*
      MulAut (LargeEvenCenterQuot (LargeEvenSzGroup ((n - 1) / 2) K))).range := by
    refine hBI.trans ?_
    rw [Subgroup.closure_le]
    intro x hx
    exact hx
  have hdvd : Nat.card B ∣ (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) := by
    refine dvd_trans (Subgroup.card_dvd_of_le hBr) (dvd_trans (Subgroup.card_range_dvd _) ?_)
    refine dvd_trans (Subgroup.card_quotient_dvd_card _) ?_
    rw [largeEvenSzGroup_eq _ K, CFSG.LieType.Ree.suzuki_order hK, hna]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnot : ¬ 3 ∣ (2 ^ n) ^ 2 * (2 ^ n - 1) * ((2 ^ n) ^ 2 + 1) :=
    TableBExc.not_dvd_card_suzuki Nat.prime_three (by norm_num)
      (three_dvd_two_pow_add_one_of_odd hlab.2.2.1)
  have h1 : Nat.card B = 1 :=
    TableBExc.card_eq_one_of_dvd_of_not_dvd (TableB.isPGroup_of_isElemAbelian hB) hdvd hnot
  rw [h1]
  norm_num

end Certs

end CFSG.StandardType.TablePThreeKG

end
