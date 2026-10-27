module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFCount
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.Quasithin.SBd19F

open Subgroup

theorem isSolvable_of_card_eq_twelve {X : Type*} [Group X] [Finite X] (h : Nat.card X = 12) :
    Group.IsSolvable X := by
  refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
  rw [h]
  have h12 : Nat.primeFactors 12 = {2, 3} := by
    have h' : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
    rw [h', Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
      Nat.Prime.primeFactors Nat.prime_three]
    rfl
  rw [h12]
  exact Finset.card_le_two

variable {P : Type*} [Group P] [Finite P] {E : Subgroup P}

theorem isSolvable_normalizer_of_card_nine (hE : Nat.card E = 9)
    (hC : ∀ x ∈ E, x ≠ 1 → centralizer ({x} : Set P) = E) :
    Group.IsSolvable ↥(normalizer (E : Set P)) := by
  refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
  have hsub : (Nat.card ↥(normalizer (E : Set P))).primeFactors ⊆ {2, 3} := by
    intro r hr
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hrd : r ∣ Nat.card ↥(normalizer (E : Set P)) := Nat.dvd_of_mem_primeFactors hr
    have : Fact r.Prime := ⟨hrp⟩
    by_contra hnot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(normalizer (E : Set P))) r hrd
    have hgo : orderOf (g : P) = r := by rw [Subgroup.orderOf_coe, hg]
    have hodd : Odd (orderOf (g : P)) := by
      rw [hgo]
      exact hrp.odd_of_ne_two hnot.1
    have hmem : (g : P) ∈ E := mem_of_odd_orderOf_of_mem_normalizer hE hC g.2 hodd
    have hdvd : r ∣ 9 := by
      rw [← hE, ← hgo]
      exact orderOf_dvd_natCard E hmem
    have hr9 : r ∣ 3 ^ 2 := by simpa using hdvd
    exact hnot.2 ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_three).mp (hrp.dvd_of_dvd_pow hr9))
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

end CFSG.Quasithin.SBd19F
