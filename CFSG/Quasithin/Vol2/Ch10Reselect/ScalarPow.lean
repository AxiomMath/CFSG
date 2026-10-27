module

public import CFSG.Quasithin.Vol2.Ch10Reselect.CardGL

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open Matrix

theorem exists_two_pow_scalar_of_pow_eq_one {K : Type*} [Field K] [Finite K] (B : GL (Fin 2) K)
    {d : ℕ} (hd : 0 < d) (hB : B ^ d = 1)
    (hodd : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ d →
      ¬ r ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K)) :
    ∃ (k : ℕ) (c : K), ((B : Matrix (Fin 2) (Fin 2) K)) ^ (2 ^ k) =
      Matrix.scalar (Fin 2) c := by
  obtain ⟨a, d', hd', rfl⟩ := Nat.exists_eq_two_pow_mul_odd hd.ne'
  have hB₁ : (B ^ (2 ^ a)) ^ d' = 1 := by
    rw [← pow_mul]
    exact hB
  have hcop : Nat.Coprime d' (Nat.card K * (Nat.card K ^ 2 - 1)) := by
    rw [← card_SL_two K]
    apply Nat.coprime_of_dvd
    intro r hr hr1 hr2
    have hr2' : r ≠ 2 := by
      rintro rfl
      exact (Odd.not_two_dvd_nat hd') hr1
    exact hodd r hr hr2' (dvd_mul_of_dvd_right hr1 _) hr2
  obtain ⟨c, hc⟩ := scalar_of_pow_eq_one_of_coprime (B ^ (2 ^ a)) hB₁ hcop
  refine ⟨a, c, ?_⟩
  rw [← Units.val_pow_eq_pow_val]
  exact hc

end CFSG.Quasithin.Vol2.Ch10Reselect
