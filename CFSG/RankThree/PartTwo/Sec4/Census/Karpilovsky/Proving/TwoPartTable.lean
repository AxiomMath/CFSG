module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving

open CFSG.EvenSporadicStandard CFSG.RankThree.PartTwo.Sec4.Census

theorem factorization_pow_mul (p k m : ℕ) [hp : Fact p.Prime] (hm : ¬ p ∣ m) (hm0 : m ≠ 0) :
    (p ^ k * m).factorization p = k := by
  rw [Nat.factorization_def _ hp.out, padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) hm0,
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm, add_zero]

theorem factorization_12_two : (12 : ℕ).factorization 2 = 2 :=
  factorization_pow_mul (p := 2) 2 3 (by norm_num) (by norm_num)

theorem factorization_6_two : (6 : ℕ).factorization 2 = 1 :=
  factorization_pow_mul (p := 2) 1 3 (by norm_num) (by norm_num)

theorem factorization_3_two : (3 : ℕ).factorization 2 = 0 :=
  factorization_pow_mul (p := 2) 0 3 (by norm_num) (by norm_num)

theorem factorization_2_two : (2 : ℕ).factorization 2 = 1 :=
  factorization_pow_mul (p := 2) 1 1 (by norm_num) (by norm_num)

theorem factorization_12_three : (12 : ℕ).factorization 3 = 1 :=
  factorization_pow_mul (p := 3) 1 4 (by norm_num) (by norm_num)

theorem factorization_6_three : (6 : ℕ).factorization 3 = 1 :=
  factorization_pow_mul (p := 3) 1 2 (by norm_num) (by norm_num)

theorem factorization_3_three : (3 : ℕ).factorization 3 = 1 :=
  factorization_pow_mul (p := 3) 1 1 (by norm_num) (by norm_num)

theorem factorization_2_three : (2 : ℕ).factorization 3 = 0 :=
  Nat.factorization_eq_zero_of_not_dvd (by norm_num)

theorem twoPartBound_eq_two_pow_factorization (s : TauCeti.SporadicName) :
    twoPartBound s = 2 ^ (sporadicMultiplierOrder s).factorization 2 := by
  cases s <;> simp [twoPartBound, sporadicMultiplierOrder, factorization_12_two,
    factorization_6_two, factorization_3_two, factorization_2_two]

theorem threePart_eq (s : TauCeti.SporadicName) :
    3 ^ (sporadicMultiplierOrder s).factorization 3 =
      if s = .M22 ∨ s = .J3 ∨ s = .McL ∨ s = .Suz ∨ s = .ONan ∨ s = .Fi22 ∨ s = .Fi24Prime
      then 3 else 1 := by
  cases s <;> simp [sporadicMultiplierOrder, factorization_12_three, factorization_6_three,
    factorization_3_three, factorization_2_three]

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving

end
