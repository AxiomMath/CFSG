module

public import CFSG.Quasithin.EmptyFaithful.R3c7Cls

public section

namespace CFSG.Quasithin.R3c7

open CFSG.Quasithin

section Main

theorem l2PrimeOnList115_holds : L2PrimeOnList115 := by
  intro K _ _ hq hty p hp hp8 hX
  have hc := ordClass_of_lemma115Type hq hty
  obtain ⟨-, -, -, hN⟩ := CFSG.Quasithin.R3c6.psl2Data hX
  have hg : Nat.gcd 2 (p ^ 1 - 1) = 2 := by
    apply Nat.gcd_eq_left
    rw [pow_one]
    have hodd : Odd p := hp.odd_of_ne_two (by omega)
    exact even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd odd_one)
  rw [hg, pow_one] at hN
  exact hc.l2p hp hp8 hN

theorem l2SquareNotOnList115_holds : L2SquareNotOnList115 := by
  intro K _ _ hq hty p hp hp3 hX
  have hc := ordClass_of_lemma115Type hq hty
  obtain ⟨-, -, -, hN⟩ := CFSG.Quasithin.R3c6.psl2Data hX
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hg : Nat.gcd 2 (p ^ 2 - 1) = 2 := by
    apply Nat.gcd_eq_left
    have hodd2 : Odd (p ^ 2) := hodd.pow
    exact even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd2 odd_one)
  have h4 : (p ^ 2) ^ 2 = p ^ 4 := by ring
  rw [hg, h4] at hN
  have h2 : p % 2 = 1 := Nat.odd_iff.1 hodd
  exact hc.false_of_l2sq hp (by omega) hN

theorem u3OddNotOnList115_holds : U3OddNotOnList115 := by
  intro K _ _ hq hty p hp hp4 hX
  have hc := ordClass_of_lemma115Type hq hty
  obtain ⟨-, -, -, -, hN⟩ := CFSG.Quasithin.R3c6.psu3Data hX
  simp only [pow_one] at hN
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    omega
  exact hc.false_of_oddLike (oddLike_of_su3 hp hp5 rfl hN)

theorem l3OddNotOnList115_holds : L3OddNotOnList115 := by
  intro K _ _ hq hty p hp hp4 hp3 hX
  have hc := ordClass_of_lemma115Type hq hty
  obtain ⟨-, -, -, -, hN⟩ := CFSG.Quasithin.R3c6.psl3Data hX
  simp only [pow_one] at hN
  exact hc.false_of_oddLike (oddLike_of_sl3 hp (by omega) rfl hN)

end Main

end CFSG.Quasithin.R3c7
