module

public import CFSG.Sporadic.Schreier.TitsAutD
public import CFSG.Sporadic.Schreier.TitsOuter

public noncomputable section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.ComponentClassification.OuterAutomorphisms

theorem factorization_card_titsD : (17971200 : ℕ).factorization 2 = 11 := by
  rw [Nat.factorization_def _ Nat.prime_two, show (17971200 : ℕ) = 2 ^ 11 * 8775 by norm_num,
    padicValNat.mul (by positivity) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by decide)]

theorem CTI_Tits_model_outer_two_part_bound
    (T : Type) [Group T] (p f : ℕ)
    (h : CFSG.Blueprint.ReeTitsModel T .Tits p f) :
    Nat.card T = 17971200 ∧ (17971200 : ℕ) = 2 ^ 11 * 8775 ∧ Nat.card (Outer T) = 2 ∧
    ordProj[2] (Nat.card T) = 2 ^ 11 ∧ 4 ≤ ordProj[2] (Nat.card T) ∧
    ordProj[2] (Nat.card (Outer T)) < ordProj[2] (Nat.card T) := by
  obtain ⟨e⟩ := titsModelEquiv T p f h
  have hT : Nat.card T = 17971200 := by rw [Nat.card_congr e.toEquiv, card_titsD]
  have hO : Nat.card (Outer T) = 2 := by
    rw [Nat.card_congr (equivalence e).toEquiv, card_outer_titsD]
  have h2 : ordProj[2] (Nat.card T) = 2 ^ 11 := by rw [hT, factorization_card_titsD]
  refine ⟨hT, by norm_num, hO, h2, by rw [h2]; norm_num, ?_⟩
  rw [hO, h2, Nat.Prime.factorization_self Nat.prime_two]
  norm_num

end CFSG.Sporadic.Schreier.Tits
