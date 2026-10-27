module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.FFC2Core
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Equiv Equiv.Perm

namespace C10P34

theorem fixed_alt5 : ∀ m : Fin 5 → ZMod 2, ∑ i, m i = 0 →
    (∀ i, m ((swap 0 1 * swap 1 2 : Perm (Fin 5))⁻¹ i) = m i) →
    (∀ i, m ((swap 2 3 * swap 3 4 : Perm (Fin 5))⁻¹ i) = m i) → m = 0 := by
  decide +kernel

theorem mem_alt_c1 : (swap 0 1 * swap 1 2 : Perm (Fin 5)) ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

theorem mem_alt_c2 : (swap 2 3 * swap 3 4 : Perm (Fin 5)) ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

theorem card_fix_cases {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5)
    (hn : n ∣ 16) (hmod : 16 ≡ n [MOD p]) : n = 16 ∨ n = 2 := by
  have hn16 : n ≤ 16 := Nat.le_of_dvd (by norm_num) hn
  have hdvd : p ∣ 16 - n := (Nat.modEq_iff_dvd' hn16).mp hmod.symm
  have hn' : n ∣ 2 ^ 4 := by norm_num; exact hn
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hn'
  have h2 : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have h3 : ¬ p ∣ 3 := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
  have h5 : ¬ p ∣ 5 := fun h => hp5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)
  interval_cases j
  · exfalso
    have h15 : p ∣ 3 * 5 := hdvd
    rcases (Nat.Prime.dvd_mul hp).mp h15 with h | h
    · exact h3 h
    · exact h5 h
  · exact Or.inr rfl
  · exfalso
    have h12 : p ∣ 2 ^ 2 * 3 := hdvd
    rcases (Nat.Prime.dvd_mul hp).mp h12 with h | h
    · exact h2 (hp.dvd_of_dvd_pow h)
    · exact h3 h
  · exfalso
    have h8 : p ∣ 2 ^ 3 := hdvd
    exact h2 (hp.dvd_of_dvd_pow h8)
  · exact Or.inl rfl

end C10P34

end CFSG.Quasithin.Vol2.Ch10.SecB
