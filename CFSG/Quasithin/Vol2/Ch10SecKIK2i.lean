module

public import CFSG.Quasithin.Vol2.Ch10SecKIK2h
public import CFSG.Quasithin.Vol2.Ch11SecA11Concl

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecA

variable {Q : Type} [Group Q] {B L : Subgroup Q} {n : ℕ}

namespace OddData

variable (hD : OddData B 168)
include hD

theorem odd21 {d o : ℕ} (ho : Odd o) (h : Nat.card ↥B = 2 ^ d * o) : o = 21 := by
  obtain ⟨a, ha⟩ := hD.card
  exact (eq_of_two_pow_mul_eq (by decide) ho
    ((show 2 ^ (a + 3) * 21 = 2 ^ a * 168 by rw [pow_add]; ring).trans (ha.symm.trans h))).symm

theorem odd21' {d o : ℕ} (ho : Odd o) (h : Nat.card (ModO2 B) = 2 ^ d * o) : o = 21 :=
  (eq_of_two_pow_mul_eq (by decide) ho
    ((show 2 ^ 3 * 21 = 168 by norm_num).trans (hD.cardQ.symm.trans h))).symm

theorem odd21_ext [Finite Q] {PV PY : ∀ (V : Type) [Group V], Prop} (h : IsExt ↥B PV PY)
    (hPV : ∀ (V : Type) [Group V] [Finite V], PV V → ∃ k, Nat.card V = 2 ^ k) {d o : ℕ}
    (ho : Odd o) (hPY : ∀ (Y : Type) [Group Y], PY Y → Nat.card Y = 2 ^ d * o) : o = 21 := by
  obtain ⟨V, _, hY, k, hk⟩ := card_of_isExt h hPV
  exact hD.odd21 ho (card_ext_eq hk (hPY _ hY))

theorem dvd_of_prime_dvd {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (h : r ∣ Nat.card ↥B) : r ∣ 168 := by
  obtain ⟨a, ha⟩ := hD.card
  rw [ha] at h
  exact ((Nat.coprime_primes hr Nat.prime_two).2 hr2).pow_right a |>.dvd_of_dvd_mul_left h

theorem eq_seven {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (h : p ∣ Nat.card ↥B) : p = 7 := by
  have h168 := hD.dvd_of_prime_dvd hp (by omega) h
  have e : (168 : ℕ) = 2 ^ 3 * 3 * 7 := by norm_num
  rw [e] at h168
  rcases (Nat.Prime.dvd_mul hp).1 h168 with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
      omega
    · have := Nat.le_of_dvd (by norm_num) h2
      omega
  · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h1

end OddData

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
