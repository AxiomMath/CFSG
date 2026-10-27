module

public import CFSG.RankThree.PartOne.K133H.SylowTorus
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.RankThree.PartOne.K133H

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.ExceptionalOrders CFSG.Open

theorem factorization_pow_sub_one {p Q k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hQ : 2 ≤ Q)
    (hd : p ∣ Q - 1) (hk : k ≠ 0) (hpk : ¬ p ∣ k) :
    (Q ^ k - 1).factorization p = (Q - 1).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  have hpQ : ¬ p ∣ Q := by
    intro h
    have h1 : p ∣ Q - (Q - 1) := Nat.dvd_sub h hd
    rw [show Q - (Q - 1) = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  have := padicValNat.pow_sub_pow (p := p) (hp.odd_of_ne_two hp2) (x := Q) (y := 1) (by omega)
    (by simpa using hd) hpQ hk
  rwa [one_pow, padicValNat.eq_zero_of_not_dvd hpk, add_zero] at this

theorem not_dvd_of_prime_ge_five {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hk : k = 2 ∨ k = 6 ∨ k = 8 ∨ k = 12) : ¬ p ∣ k := by
  intro h
  have hle : p ≤ k := Nat.le_of_dvd (by omega) h
  have hk12 : p ≤ 12 := by omega
  interval_cases p <;> rcases hk with rfl | rfl | rfl | rfl <;> first | omega | (norm_num at hp)

theorem factorization_ordF4 {p Q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hQ : 2 ≤ Q)
    (hd : p ∣ Q - 1) : (ordF4 Q).factorization p = 4 * (Q - 1).factorization p := by
  have hp2 : p ≠ 2 := by omega
  have hpQ : ¬ p ∣ Q := by
    intro h
    have h1 : p ∣ Q - (Q - 1) := Nat.dvd_sub h hd
    rw [show Q - (Q - 1) = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hne : ∀ k, k ≠ 0 → Q ^ k - 1 ≠ 0 := fun k hk =>
    Nat.sub_ne_zero_of_lt (lt_of_lt_of_le (by omega : 1 < Q) (Nat.le_self_pow hk Q))
  have h12 := factorization_pow_sub_one hp hp2 hQ hd (by norm_num : (12 : ℕ) ≠ 0)
    (not_dvd_of_prime_ge_five hp hp5 (Or.inr (Or.inr (Or.inr rfl))))
  have h8 := factorization_pow_sub_one hp hp2 hQ hd (by norm_num : (8 : ℕ) ≠ 0)
    (not_dvd_of_prime_ge_five hp hp5 (Or.inr (Or.inr (Or.inl rfl))))
  have h6 := factorization_pow_sub_one hp hp2 hQ hd (by norm_num : (6 : ℕ) ≠ 0)
    (not_dvd_of_prime_ge_five hp hp5 (Or.inr (Or.inl rfl)))
  have h2 := factorization_pow_sub_one hp hp2 hQ hd (by norm_num : (2 : ℕ) ≠ 0)
    (not_dvd_of_prime_ge_five hp hp5 (Or.inl rfl))
  have hQ24 : Q ^ 24 ≠ 0 := by positivity
  have e12 := hne 12 (by norm_num)
  have e8 := hne 8 (by norm_num)
  have e6 := hne 6 (by norm_num)
  have e2 := hne 2 (by norm_num)
  unfold ordF4
  rw [Nat.factorization_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hQ24 e12) e8) e6) e2,
    Nat.factorization_mul (mul_ne_zero (mul_ne_zero hQ24 e12) e8) e6,
    Nat.factorization_mul (mul_ne_zero hQ24 e12) e8, Nat.factorization_mul hQ24 e12]
  simp only [Finsupp.add_apply]
  rw [h12, h8, h6, h2, Nat.factorization_eq_zero_of_not_dvd (fun h => hpQ (hp.dvd_of_dvd_pow h))]
  ring

variable {K : Type} [Field K]

set_option linter.unusedSectionVars false

theorem torusGroup_le_adjointGroup' {τ : Tag} : torusGroup τ K ≤ adjointGroup τ K :=
  (Subgroup.closure_le _).2 fun _ ⟨p, hp⟩ => hp ▸ torusElt_mem_adjointGroup p.1 p.2

theorem exists_conj_into_torus_F4 [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K - 1) {A : Subgroup (ModGL .F4 K)} (hAC : A ≤ adjointGroup .F4 K)
    (hpow : ∀ x ∈ A, x ^ p = 1) :
    ∃ g ∈ adjointGroup .F4 K, A.map (MulAut.conj g).toMonoidHom ≤ torusGroup .F4 K := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hQ : 2 ≤ Nat.card K := Finite.one_lt_card
  refine exists_conj_le_of_sylow (p := p) torusGroup_le_adjointGroup' hAC hpow ?_
  rw [card_adjointGroup_F4, card_torusGroup_F4, factorization_ordF4 hp hp5 hQ hpq,
    Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]

end CFSG.RankThree.PartOne.K133H
