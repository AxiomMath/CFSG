module

public import CFSG.Quasithin.Vol2.Ch10SecKIK2q
public import CFSG.Quasithin.Vol2.Ch10SecKIK2e
public import CFSG.Quasithin.Vol2.Ch10SecKIK2o

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecA CFSG.Blueprint

variable {X : Type} [Group X] {M : ℕ}

theorem false_of_psl2p (hJ : B56Card M) (hc : Nat.card X = M ∨ Nat.card X = 3 * M) {p : ℕ}
    (hp : p.Prime) (hp5 : p % 5 = 1 ∨ p % 5 = 4) (hp8 : p % 8 = 3 ∨ p % 8 = 5)
    (h : IsPSL 2 p 1 X) : False := by
  have hp2 : p ≠ 2 := by omega
  have h2 := two_mul_card_of_isPSL_two hp hp2 h
  have h16X : ¬ 16 ∣ Nat.card X := fun h16 =>
    not_sixteen_dvd hp8 (h2 ▸ dvd_mul_of_dvd_right h16 2)
  have h16M : ¬ 16 ∣ M := fun h16 => h16X (by
    rcases hc with hc | hc <;> rw [hc]
    · exact h16
    · exact dvd_mul_of_dvd_right h16 3)
  have hpX : p ∣ Nat.card X :=
    ((Nat.coprime_primes hp Nat.prime_two).2 hp2).dvd_of_dvd_mul_left (Dvd.intro _ h2.symm)
  have hpM : p ∣ M := by
    rcases hc with hc | hc <;> rw [hc] at hpX
    · exact hpX
    · exact ((Nat.coprime_primes hp (by norm_num)).2 (by omega)).dvd_of_dvd_mul_left hpX
  have := le_seven_of_dvd hp (hpM.trans (dvd_of_b56Card hJ h16M))
  omega

theorem goodLie_of_rank2 (hJ : B56Card M) (hc : Nat.card X = M ∨ Nat.card X = 3 * M)
    (h : IsRank2LieChar2 X) : GoodLie X := by
  rcases h with ⟨f, h | h | h | h | ⟨-, h⟩ | ⟨-, -, h⟩⟩ | h
  · exact ⟨f, Or.inl h⟩
  · exact ⟨f, Or.inr (Or.inl h)⟩
  · exact ⟨f, Or.inr (Or.inr (Or.inl h))⟩
  · exact ⟨f, Or.inr (Or.inr (Or.inr h))⟩
  · exact (false_of_3D4 hJ hc h).elim
  · exact (false_of_2F4 hJ hc h).elim
  · exact (false_of_tits hJ hc h).elim


theorem classify15 (hJ : B56Card M) (hc : Nat.card X = M ∨ Nat.card X = 3 * M)
    (h : Out15 X) : IsAlt 7 X ∨ IsHat X ↥(alternatingGroup (Fin 7)) := by
  rcases h with h | ⟨p, hp, hp5, hp8, h⟩ | h
  · exact h
  · exact (false_of_psl2p hJ hc hp hp5 hp8 h).elim
  · exact (false_of_badConc hJ hc h).elim

theorem classify168 (hJ : B56Card M) (hc : Nat.card X = M ∨ Nat.card X = 3 * M)
    (h : Out168 X) :
    (IsPSL 4 2 1 X ∨ IsPSL 5 2 1 X) ∨ (IsAlt 7 X ∨ IsHat X ↥(alternatingGroup (Fin 7))) := by
  rcases out168 h with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (false_of_badConc hJ hc h).elim

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
