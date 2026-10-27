module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.Quasithin.H13.S126P31

private theorem index_le_three_aux {i n : ℕ} (hi : i ∣ n) (hn : n ≠ 0) (hodd : ¬ 2 ∣ i)
    (hp : ∀ p : ℕ, p.Prime → p ∣ n → p = 2 ∨ p = 3) (h9 : ¬ 9 ∣ n) : i ≤ 3 := by
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hn (zero_dvd_iff.mp hi)
  have hprime : ∀ {d : ℕ}, d.Prime → d ∣ i → d = 3 := by
    intro d hd hdi
    rcases hp d hd (hdi.trans hi) with h2 | h3
    · subst h2
      exact absurd hdi hodd
    · exact h3
  obtain ⟨k, hk⟩ : ∃ k, i = 3 ^ k := ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hi0 hprime⟩
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · calc i = 3 ^ k := hk
      _ ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 3 := by norm_num
  · exfalso
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have h9i : 9 ∣ i := ⟨3 ^ j, by rw [hk]; ring⟩
    exact h9 (h9i.trans hi)

theorem card_le_six_of_primes {C : Type*} [Group C] [Finite C]
    (hp : ∀ p : ℕ, p.Prime → p ∣ Nat.card C → p = 2 ∨ p = 3)
    (h9 : ¬ 9 ∣ Nat.card C)
    (hO2 : ∀ N : Subgroup C, N.Normal → IsPGroup 2 N → N = ⊥) :
    Nat.card C ≤ 6 := by
  obtain ⟨P⟩ : Nonempty (Sylow 2 C) := Sylow.nonempty
  obtain ⟨H, hHp, hodd⟩ : ∃ H : Subgroup C, IsPGroup 2 H ∧ ¬ 2 ∣ H.index :=
    ⟨(P : Subgroup C), P.isPGroup', Sylow.not_dvd_index P⟩
  have hdvd : H.index ∣ Nat.card C := Dvd.intro_left _ (Subgroup.card_mul_index H)
  have hi3 : H.index ≤ 3 := index_le_three_aux hdvd Nat.card_pos.ne' hodd hp h9
  have hcore : H.normalCore = ⊥ :=
    hO2 H.normalCore H.normalCore_normal (hHp.to_le H.normalCore_le)
  have hbound : H.normalCore.index ≤ Nat.factorial H.index :=
    H.index_normalCore_le_factorial_index
  rw [hcore, Subgroup.index_bot] at hbound
  calc Nat.card C ≤ Nat.factorial H.index := hbound
    _ ≤ Nat.factorial 3 := Nat.factorial_le hi3
    _ = 6 := rfl

end CFSG.Quasithin.H13.S126P31
