module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSporDef

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Open CFSG.QuasithinUnique

theorem not_three_dvd_pow_mul_two_pow {p a k : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ¬ 3 ∣ p ^ a * 2 ^ k := by
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h1 | h1
  · have h2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
      (Nat.prime_three.dvd_of_dvd_pow h1)
    omega
  · have h2 := Nat.prime_three.dvd_of_dvd_pow h1
    omega

theorem pow_mul_two_pow_ne_two_pow {p a k j : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (ha : 0 < a) :
    p ^ a * 2 ^ k ≠ 2 ^ j := by
  intro h
  have h1 : p ∣ 2 ^ j := h ▸ ((dvd_pow_self p ha.ne').mul_right (2 ^ k))
  have h2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1)
  omega

theorem isSylowTwoOf_top_of {X : Type*} [Group X] {S : Subgroup X} (h2 : IsPGroup 2 S)
    (hi : ¬ 2 ∣ S.index) : IsSylowTwoOf S ⊤ :=
  ⟨le_top, h2, by rw [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S]
                  exact hi⟩

theorem noPowerOvergroup_of_overgroups {F : ∀ (X : Type) [Group X], Prop}
    (h3 : ∀ (X : Type) [Group X] [Finite X], F X → 3 ∣ Nat.card X)
    (hov : ∀ (X : Type) [Group X] [Finite X], F X → ∀ T Y : Subgroup X, IsSylowTwoOf T ⊤ →
      T ≤ Y → Y = ⊤ ∨ (∃ j, Nat.card Y = 2 ^ j) ∨ 3 ∣ Nat.card Y) : NoPowerOvergroup F := by
  intro X _ _ hX p a hp h5 ha H S hS2 hSi hSH hH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS2
  have hapos : 0 < a := by omega
  have hH' : Nat.card H = p ^ a * 2 ^ k := by rw [hH, hk]
  rcases hov X hX S H (isSylowTwoOf_top_of hS2 hSi) hSH with htop | ⟨j, hj⟩ | h3'
  · have hcard : Nat.card H = Nat.card X := by rw [htop]; exact Subgroup.card_top
    exact not_three_dvd_pow_mul_two_pow hp h5 (hH' ▸ hcard ▸ h3 X hX)
  · exact pow_mul_two_pow_ne_two_pow hp h5 hapos (hH' ▸ hj)
  · exact not_three_dvd_pow_mul_two_pow hp h5 (hH' ▸ h3')

end CFSG.Quasithin.H13.NQCore
