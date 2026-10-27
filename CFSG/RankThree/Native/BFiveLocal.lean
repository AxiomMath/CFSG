module

public import CFSG.Monster.Existence.BabyOrder
public import CFSG.Monster.B.Pinned.Primes.SeedGL
public import CFSG.RankThree.Native.FiveLocalBasic

public section

namespace CFSG.RankThree.Native

open CFSG.Monster.B CFSG.Monster.B.Pinned CFSG.Blueprint FiveLocal
open CFSG.Monster.Existence (eB betaStd betaStd_explicit betaRow_eB card_nativeB)

instance bFiveFinite : Finite NativeSporadic.B := finite_B

instance bFiveFiniteS : Finite Sbp := Finite.of_equiv _ eB.toEquiv

theorem factorization_card_B_five : (Nat.card NativeSporadic.B).factorization 5 = 6 := by
  rw [card_nativeB, CFSG.Open.monsterBabyOrder,
    show 2 ^ 41 * 3 ^ 13 * 5 ^ 6 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 31 * 47 =
      5 ^ 6 * (2 ^ 41 * 3 ^ 13 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 31 * 47) by ring,
    Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_five, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

end CFSG.RankThree.Native
