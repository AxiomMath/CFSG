module

public import CFSG.RankThree.PartOne.KS.Basic

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem not_sq_dvd_mul_of_coprime {p s m B : ℕ} (hp : p.Prime) (hps : Nat.Coprime p s)
    (hmB : m < (B + 1) ^ 2) (hm : ∀ q : ℕ, q ≤ B → 2 ≤ q → ¬ q ^ 2 ∣ m) (hm0 : 0 < m) :
    ¬ p ^ 2 ∣ s * m := by
  intro h
  have hc : Nat.Coprime (p ^ 2) s := Nat.Coprime.pow_left 2 hps
  have h' : p ^ 2 ∣ m := hc.dvd_of_dvd_mul_left h
  have hle : p ^ 2 ≤ m := Nat.le_of_dvd hm0 h'
  have hpB : p ≤ B := by
    by_contra hcon
    have : (B + 1) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  exact hm p hpB hp.two_le h'

theorem not_sq_dvd_two_pow_three_pow_mul {p a b m B : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hmB : m < (B + 1) ^ 2) (hm : ∀ q : ℕ, q ≤ B → 2 ≤ q → ¬ q ^ 2 ∣ m) (hm0 : 0 < m) :
    ¬ p ^ 2 ∣ 2 ^ a * 3 ^ b * m := by
  have h2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
  have h3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).mpr (by omega)
  exact not_sq_dvd_mul_of_coprime hp (Nat.Coprime.mul_right (Nat.Coprime.pow_right a h2)
    (Nat.Coprime.pow_right b h3)) hmB hm hm0

theorem coprime_two_three_five_pow {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hp5 : p ≠ 5)
    (a b c : ℕ) : Nat.Coprime p (2 ^ a * 3 ^ b * 5 ^ c) := by
  have h2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
  have h3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).mpr (by omega)
  have h5 : Nat.Coprime p 5 := (Nat.coprime_primes hp Nat.prime_five).mpr hp5
  exact Nat.Coprime.mul_right (Nat.Coprime.mul_right (Nat.Coprime.pow_right a h2)
    (Nat.Coprime.pow_right b h3)) (Nat.Coprime.pow_right c h5)

theorem not_sq_dvd_card_mulAut_of_outer_le {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hnab : ∃ a b : T, a * b ≠ b * a) {A : Type} [Group A] (e : T ≃* A) {N k p : ℕ}
    (hN : Nat.card A = N) (hk : Nat.card (Outer A) ≤ k) (hp : p.Prime) (hpk : k < p)
    (hpN : ¬ p ^ 2 ∣ N) : ¬ p ^ 2 ∣ Nat.card (MulAut T) := by
  have hc : center T = ⊥ := center_eq_bot_of_simple hnab
  have : Finite (MulAut T) := Finite.of_injective (fun f : MulAut T => (f : T → T))
    fun f g h => MulEquiv.ext (congrFun h)
  rw [card_mulAut_eq_mul_card_outer hc]
  have hout : Nat.card (Outer T) = Nat.card (Outer A) :=
    Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv
  have hT : Nat.card T = N := (Nat.card_congr e.toEquiv).trans hN
  have hpos : 0 < Nat.card (Outer T) := Nat.card_pos
  rw [hT]
  intro h
  have hnd : ¬ p ∣ Nat.card (Outer T) := fun hd => by
    have := Nat.le_of_dvd hpos hd
    omega
  have hcop : Nat.Coprime (p ^ 2) (Nat.card (Outer T)) :=
    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)
  exact hpN (hcop.dvd_of_dvd_mul_right h)

end CFSG.RankThree.PartOne
