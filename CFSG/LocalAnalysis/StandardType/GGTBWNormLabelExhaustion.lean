module

public import CFSG.LocalAnalysis.StandardType.GGTBWNorm

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggTBWNormLabelRest_holds : GGTBWNormLabelRest := by
  intro p hp hp2 lab hLab hExcl hN1 hE8q4five hE8minusFive hBCq2 hLow hSmall hClass
    hSymp hLinPlus hE6Minus hUnitMinus hTwE6Plus hUnitCoprime hTri hTwE6 hOrthSigned
    hTwE6Minus hE6Plus hLinCoprime hOrthOdd hUnitPrime hLinPrime hE8Minus hE7Minus
    hE8Plus hE7Plus hRee hExcSmall hOrthEven hOrthFour hLinTwice hLinThrice hLinFour
    hUnitTwice hE8PhiSix hE8Quartic hE6PhiThree hE8PhiThree hE8Three hE7Three
    hLinNonSplit hE7Six hE8PlusFive hSympNonSplit hOrthNonSplit hTwE6PhiSix
    hUnitNonSplit hUnitFour hUnitFive hLinFive hUnitThree hLinThree hUnitThrice hUnitNine
    hE6Three hLinNine
  classical
  let q := 2 ^ lab.n
  have hq : 1 ≤ q := by
    have hpos : 0 < q := by dsimp [q]; positivity
    omega
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hp6 : p ≠ 6 := by rintro rfl; norm_num at hp
  have hpm {x : ℕ} (hx : p ∣ x ^ 2 - 1) : p ∣ x - 1 ∨ p ∣ x + 1 := by
    have heq : x ^ 2 - 1 = (x + 1) * (x - 1) := by
      simpa only [one_pow] using Nat.sq_sub_sq x 1
    rw [heq] at hx
    exact (hp.dvd_mul.mp hx).symm
  have hthree (hx : p ∣ q ^ 3 - 1) : p ∣ q - 1 ∨ p ∣ q ^ 2 + q + 1 := by
    have heq : q ^ 3 - 1 = (q ^ 2 + q + 1) * (q - 1) := by
      simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc] using
        (geom_sum_mul_of_one_le hq 3).symm
    rw [heq] at hx
    exact (hp.dvd_mul.mp hx).symm
  have hthreePlus (hx : p ∣ q ^ 3 + 1) : p ∣ q + 1 ∨ p ∣ q ^ 2 - q + 1 := by
    have hq2 : q ≤ q ^ 2 := by nlinarith
    have heq : q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
      nlinarith [congrArg (fun x : ℕ => x * (q + 1)) (Nat.sub_add_cancel hq2)]
    rw [heq] at hx
    exact hp.dvd_mul.mp hx
  have hfive : ¬ 5 ∣ q ^ 2 + q + 1 := by
    intro hd
    have hz := (ZMod.natCast_eq_zero_iff (q ^ 2 + q + 1) 5).mpr hd
    have hz' : (q : ZMod 5) ^ 2 + q + 1 = 0 := by simpa using hz
    exact (show ∀ a : ZMod 5, a ^ 2 + a + 1 ≠ 0 from by decide +kernel) _ hz'
  have hpFour : ¬ p ∣ 4 := by
    intro hd
    have hd' : p ∣ 2 ^ 2 := by norm_num; exact hd
    exact hp2 (Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two hd')
  cases ht : lab.tag with
  | A =>
    have hr3 : 3 ≤ lab.rank := by
      by_contra h
      exact hLow (Or.inl ⟨ht, by omega⟩)
    have hsq : p ∣ q ^ 2 - 1 := by
      by_contra h
      exact hLinNonSplit ⟨Or.inl ht, hr3, h⟩
    obtain hm | hm := hpm hsq
    · have hdim : p ∣ lab.rank + 1 := by
        by_contra h
        exact hLinCoprime ⟨Or.inl ht, hr3, hm, h⟩
      rcases hdim with ⟨m, hdim⟩
      by_cases hpEq : p = 3
      · subst p
        have hne6 : lab.rank + 1 ≠ 6 := by
          intro he
          exact hLinTwice ⟨ht, by omega, hm⟩
        have hne9 : lab.rank + 1 ≠ 9 := by
          intro he
          exact hLinNine ⟨ht, rfl, he, hm⟩
        have hd12 : 12 ≤ lab.rank + 1 := by omega
        exact (hLinThree ⟨ht, rfl, ⟨m, hdim⟩, hd12, hm⟩).elim
      · have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hpEq
        have hm4 : m ≤ 4 := by
          by_contra h
          exact hLinFive ⟨ht, hp5, ⟨m, hdim⟩, by nlinarith, hm⟩
        interval_cases m
        · omega
        · exact (hLinPrime ⟨ht, hp5, by omega, hm⟩).elim
        · exact (hLinTwice ⟨ht, by omega, hm⟩).elim
        · exact (hLinThrice ⟨ht, hp5, by omega, hm⟩).elim
        · exact (hLinFour ⟨ht, hp5, by omega, hm⟩).elim
    · exact (hLinPlus ⟨Or.inl ht, hr3, hm⟩).elim
  | twA =>
    have hr2 : 2 ≤ lab.rank := by
      have hh := hLab.2
      simp only [ht] at hh
      exact hh.1
    have hr3 : 3 ≤ lab.rank := by
      by_contra h
      exact hLow (Or.inr ⟨Or.inl ht, by omega⟩)
    have hsq : p ∣ q ^ 2 - 1 := by
      by_contra h
      exact hUnitNonSplit ⟨Or.inl ht, hr3, h⟩
    obtain hm | hm := hpm hsq
    · exact (hUnitMinus ⟨Or.inl ht, hr3, hm⟩).elim
    · have hdim : p ∣ lab.rank + 1 := by
        by_contra h
        exact hUnitCoprime ⟨Or.inl ht, hr3, hm, h⟩
      rcases hdim with ⟨m, hdim⟩
      by_cases hpEq : p = 3
      · subst p
        have hne6 : lab.rank + 1 ≠ 6 := by
          intro he
          exact hUnitTwice ⟨ht, by omega, hm⟩
        have hne9 : lab.rank + 1 ≠ 9 := by
          intro he
          exact hUnitNine ⟨ht, rfl, he, hm⟩
        have hd12 : 12 ≤ lab.rank + 1 := by omega
        exact (hUnitThree ⟨ht, rfl, ⟨m, hdim⟩, hd12, hm⟩).elim
      · have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hpEq
        have hm4 : m ≤ 4 := by
          by_contra h
          exact hUnitFive ⟨ht, hp5, ⟨m, hdim⟩, by nlinarith, hm⟩
        interval_cases m
        · omega
        · exact (hUnitPrime ⟨ht, hp5, by omega, hm⟩).elim
        · exact (hUnitTwice ⟨ht, by omega, hm⟩).elim
        · exact (hUnitThrice ⟨ht, hp5, by omega, hm⟩).elim
        · exact (hUnitFour ⟨ht, hp5, by omega, hm⟩).elim
  | B | C =>
    have htbc : lab.tag = .B ∨ lab.tag = .C := by simp [ht]
    have hr2 : 2 ≤ lab.rank := by
      have hh := hLab.2
      simp only [ht] at hh
      exact hh.1
    have hr3 : 3 ≤ lab.rank := by
      by_contra h
      exact hExcl (Or.inr ⟨htbc, by omega⟩)
    have hsq : p ∣ q ^ 2 - 1 := by
      by_contra h
      exact hSympNonSplit ⟨htbc, hr3, h⟩
    exact (hSymp ⟨htbc, hr3, hpm hsq⟩).elim
  | D =>
    have hr3 : 3 ≤ lab.rank := by simpa only [ht] using hLab.2
    by_cases h3 : lab.rank = 3
    · have hsq : p ∣ q ^ 2 - 1 := by
        by_contra h
        exact hLinNonSplit ⟨Or.inr ⟨ht, h3⟩, hr3, h⟩
      obtain hm | hm := hpm hsq
      · exact (hLinCoprime ⟨Or.inr ⟨ht, h3⟩, hr3, hm, by simpa [h3] using hpFour⟩).elim
      · exact (hLinPlus ⟨Or.inr ⟨ht, h3⟩, hr3, hm⟩).elim
    · have hr4 : 4 ≤ lab.rank := by omega
      have hsq : p ∣ q ^ 2 - 1 := by
        by_contra h
        exact hOrthNonSplit ⟨Or.inl ht, hr4, h⟩
      have hs := hpm hsq
      by_cases h4 : lab.rank = 4
      · exact (hOrthFour ⟨ht, h4, hs⟩).elim
      rcases Nat.even_or_odd lab.rank with he | ho
      · have h5 : lab.rank ≠ 5 := by intro hh; norm_num [hh] at he
        have hr6 : 6 ≤ lab.rank := by omega
        exact (hOrthEven ⟨ht, hr6, he, hs⟩).elim
      · have hr5 : 5 ≤ lab.rank := by omega
        rcases hs with hm | hm
        · exact (hOrthOdd (Or.inl ⟨ht, hr5, ho, hm⟩)).elim
        · exact (hOrthSigned (Or.inl ⟨ht, hr5, ho, hm⟩)).elim
  | twD =>
    have hr2 : 2 ≤ lab.rank := by simpa only [ht] using hLab.2
    have hr3 : 3 ≤ lab.rank := by
      by_contra h
      exact hLow (Or.inr ⟨Or.inr ht, by omega⟩)
    by_cases h3 : lab.rank = 3
    · have hsq : p ∣ q ^ 2 - 1 := by
        by_contra h
        exact hUnitNonSplit ⟨Or.inr ⟨ht, h3⟩, hr3, h⟩
      obtain hm | hm := hpm hsq
      · exact (hUnitMinus ⟨Or.inr ⟨ht, h3⟩, hr3, hm⟩).elim
      · exact (hUnitCoprime ⟨Or.inr ⟨ht, h3⟩, hr3, hm, by simpa [h3] using hpFour⟩).elim
    · have hr4 : 4 ≤ lab.rank := by omega
      have hsq : p ∣ q ^ 2 - 1 := by
        by_contra h
        exact hOrthNonSplit ⟨Or.inr ht, hr4, h⟩
      rcases hpm hsq with hm | hm
      · exact (hOrthSigned (Or.inr ⟨ht, hr4, Or.inl hm⟩)).elim
      · rcases Nat.even_or_odd lab.rank with he | ho
        · exact (hOrthSigned (Or.inr ⟨ht, hr4, Or.inr ⟨he, hm⟩⟩)).elim
        · have h4 : lab.rank ≠ 4 := by intro hh; norm_num [hh] at ho
          have hr5 : 5 ≤ lab.rank := by omega
          exact (hOrthOdd (Or.inr ⟨ht, hr5, ho, hm⟩)).elim
  | E6 =>
    have hpNe3 : p ≠ 3 := fun hh => hE6Three ⟨ht, hh⟩
    have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hpNe3
    by_cases hsq : p ∣ q ^ 2 - 1
    · rcases hpm hsq with hm | hm
      · exact (hE6Minus ⟨ht, hp5, hm⟩).elim
      · exact (hE6Plus ⟨ht, hp5, hm⟩).elim
    · have hcube : p ∣ q ^ 3 - 1 := by
        by_contra h
        exact hExcSmall (Or.inr (Or.inr (Or.inl ⟨ht, hsq, h⟩)))
      rcases hthree hcube with hm | hm
      · exact (hE6Minus ⟨ht, hp5, hm⟩).elim
      · have hpNe5 : p ≠ 5 := by intro hh; exact hfive (by simpa [hh] using hm)
        have hp7 : 7 ≤ p := by omega
        exact (hE6PhiThree ⟨ht, hp7, hm⟩).elim
  | E7 =>
    have hpNe3 : p ≠ 3 := fun hh => hE7Three ⟨ht, hh⟩
    have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hpNe3
    by_cases hsq : p ∣ q ^ 2 - 1
    · rcases hpm hsq with hm | hm
      · exact (hE7Minus ⟨ht, hp5, hm⟩).elim
      · exact (hE7Plus ⟨ht, hp5, hm⟩).elim
    · by_cases hsix : p ∣ q ^ 6 - 1
      · exact (hE7Six ⟨ht, hp5, hsix, hsq⟩).elim
      · exact (hExcSmall (Or.inr (Or.inl ⟨ht, hsix⟩))).elim
  | E8 =>
    have hpNe3 : p ≠ 3 := fun hh => hE8Three ⟨ht, hh⟩
    have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hpNe3
    have hminus : ¬ p ∣ q - 1 := by
      intro hm
      by_cases hh : p = 5
      · exact hE8minusFive ⟨ht, hh, by simpa [hh] using hm⟩
      · exact hE8Minus ⟨ht, by omega, hm⟩
    have hplus : ¬ p ∣ q + 1 := by
      intro hm
      by_cases hh : p = 5
      · exact hE8PlusFive ⟨ht, hh, by simpa [hh] using hm⟩
      · exact hE8Plus ⟨ht, by omega, hm⟩
    have hsq : ¬ p ∣ q ^ 2 - 1 := by
      intro hd
      exact (hpm hd).elim hminus hplus
    by_cases hfour : p ∣ q ^ 4 - 1
    · have hd : p ∣ (q ^ 2) ^ 2 - 1 := by simpa [← pow_mul] using hfour
      obtain hd | hd := hpm hd
      · exact (hsq hd).elim
      · by_cases hh : p = 5
        · exact (hE8q4five ⟨ht, hh, by simpa [hh] using hd⟩).elim
        · exact (hE8Quartic ⟨ht, by omega, hd⟩).elim
    · by_cases hsix : p ∣ q ^ 6 - 1
      · have hd : p ∣ (q ^ 3) ^ 2 - 1 := by simpa [← pow_mul] using hsix
        obtain hd | hd := hpm hd
        · obtain hd | hd := hthree hd
          · exact (hminus hd).elim
          · exact (hE8PhiThree ⟨ht, hpNe3, hd⟩).elim
        · obtain hd | hd := hthreePlus hd
          · exact (hplus hd).elim
          · exact (hE8PhiSix ⟨ht, hpNe3, hd⟩).elim
      · exact (hExcSmall (Or.inl ⟨ht, hfour, hsix⟩)).elim
  | F4 => exact (hExcl (Or.inl ht)).elim
  | twE6 => exact (hTwE6 ht).elim
  | triD4 => exact (hTri ht).elim
  | twF4 => exact (hRee ht).elim
  | G2 | twB2 | B2der | G2der | twF4der =>
    exact (hSmall (by simp [GGTableBNbrInnerNineSmallLabel, ht])).elim

end CFSG.StandardType

end
