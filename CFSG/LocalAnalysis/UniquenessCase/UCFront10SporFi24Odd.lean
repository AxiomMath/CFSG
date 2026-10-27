module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24TCent
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporFi24ECard
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporOdd
import CFSG.GroupTheory.ElementaryAbelianTransport
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import CFSG.CGT.Timmesfeld75.Statements
import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
import CFSG.LocalAnalysis.RankThreeUC.Asc1930
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporK105In
import CFSG.Quasithin.Background.A1bGroups
import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

namespace Fi24K

open Subgroup CFSG.Blueprint CFSG.Sporadic.Fi24

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem fi24_odd
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (A : Subgroup J) (hA : CFSG.Open.IsElemAbelian p A) (hA1 : A ≠ ⊥)
    (hTA : fi24T ≤ Subgroup.normalizer (A : Set J)) :
    A ⊓ Subgroup.centralizer {fi24z} ≠ ⊥ := by
  intro hAz
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hTp : IsPGroup 2 fi24T := IsPGroup.of_card (p := 2) (n := 21) card_fi24T
  have hzT : fi24z ∈ fi24T := fi24E_le_fi24T fi24z_mem
  have hzz : fi24z * fi24z = 1 := by
    have h := fi24E_sq fi24z fi24z_mem
    rwa [pow_two] at h
  have hZ : ∀ t ∈ fi24T, (∀ s ∈ fi24T, s * t = t * s) → t = 1 ∨ t = fi24z :=
    fun t _ hc => eq_one_or_eq_fi24z hc
  obtain ⟨n, hn⟩ := (CFSG.Open.IsElemAbelian.isPGroup hA).exists_card_eq
  have h2 : 2 ^ 21 ∣ Nat.card (GL (Fin n) (ZMod p)) := by
    rw [← card_fi24T]
    exact card_dvd_card_GL_of_inf_centralizer_eq_bot hp (by omega) hTp hzT hzz hZ hA hn hA1 hTA hAz
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hA1 (Subgroup.card_eq_one.1 (by rw [hn, pow_zero]))
  have hfac : (1255205709190661721292800 : ℕ) =
      2 ^ 21 * 3 ^ 16 * 5 ^ 2 * 7 ^ 3 * 11 * 13 * 17 * 23 * 29 := by norm_num
  have hdvdJ : p ^ n ∣ 2 ^ 21 * 3 ^ 16 * 5 ^ 2 * 7 ^ 3 * 11 * 13 * 17 * 23 * 29 := by
    rw [← hfac, ← card_J, ← hn]
    exact Subgroup.card_subgroup_dvd_card A
  have hpJ := (dvd_pow_self p hn0).trans hdvdJ
  have hpq : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq h =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 h
  have hp' : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 23 ∨ p = 29 := by
    rcases (Nat.Prime.dvd_mul hp).1 hpJ with h | h29
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h23
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h17
        · rcases (Nat.Prime.dvd_mul hp).1 h with h | h13
          · rcases (Nat.Prime.dvd_mul hp).1 h with h | h11
            · rcases (Nat.Prime.dvd_mul hp).1 h with h | h7
              · rcases (Nat.Prime.dvd_mul hp).1 h with h | h5
                · rcases (Nat.Prime.dvd_mul hp).1 h with h2 | h3
                  · have := hpq 2 Nat.prime_two (hp.dvd_of_dvd_pow h2)
                    omega
                  · have := hpq 3 Nat.prime_three (hp.dvd_of_dvd_pow h3)
                    omega
                · exact Or.inl (hpq 5 (by norm_num) (hp.dvd_of_dvd_pow h5))
              · exact Or.inr (Or.inl (hpq 7 (by norm_num) (hp.dvd_of_dvd_pow h7)))
            · exact Or.inr (Or.inr (Or.inl (hpq 11 (by norm_num) h11)))
          · exact Or.inr (Or.inr (Or.inr (Or.inl (hpq 13 (by norm_num) h13))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hpq 17 (by norm_num) h17)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (hpq 23 (by norm_num) h23))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (hpq 29 (by norm_num) h29))))))
  have hle : ∀ k : ℕ,
      ¬ p ^ (k + 1) ∣ 2 ^ 21 * 3 ^ 16 * 5 ^ 2 * 7 ^ 3 * 11 * 13 * 17 * 23 * 29 →
      n ≤ k := fun k hk => by
    by_contra h
    exact hk ((pow_dvd_pow p (by omega)).trans hdvdJ)
  rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hn2 := hle 2 (by norm_num)
    interval_cases n <;> rw [Matrix.card_GL_field] at h2 <;>
      norm_num [ZMod.card, Fin.prod_univ_succ] at h2
  · have hn3 := hle 3 (by norm_num)
    interval_cases n <;> rw [Matrix.card_GL_field] at h2 <;>
      norm_num [ZMod.card, Fin.prod_univ_succ] at h2
  · have hn1 := hle 1 (by norm_num)
    interval_cases n <;> rw [Matrix.card_GL_field] at h2 <;>
      norm_num [ZMod.card, Fin.prod_univ_succ] at h2
  · have hn1 := hle 1 (by norm_num)
    interval_cases n <;> rw [Matrix.card_GL_field] at h2 <;>
      norm_num [ZMod.card, Fin.prod_univ_succ] at h2
  · have hn1 := hle 1 (by norm_num)
    interval_cases n <;> rw [Matrix.card_GL_field] at h2 <;>
      norm_num [ZMod.card, Fin.prod_univ_succ] at h2
  · have hn1 := hle 1 (by norm_num)
    interval_cases n <;> rw [Matrix.card_GL_field] at h2 <;>
      norm_num [ZMod.card, Fin.prod_univ_succ] at h2
  · have hn1 := hle 1 (by norm_num)
    interval_cases n <;> rw [Matrix.card_GL_field] at h2 <;>
      norm_num [ZMod.card, Fin.prod_univ_succ] at h2

end Fi24K

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
