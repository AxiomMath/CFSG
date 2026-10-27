module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Chev2GlueReduction
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20k
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Sporadic.Schreier.TitsCert
public import CFSG.GroupTheory.PermutingProducts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteenR
public import CFSG.Quasithin.Background.HTriPermute

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ASVolI.ChIJK (IsSplitBNPair)

theorem le_normalizer_or_fermat_of_splitBN {K : Type} [Group K] [Finite K] {B N : Subgroup K}
    (hBN : IsSplitBNPair 2 B N) (U : Sylow 2 K) {E : Subgroup K} {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hcard : Nat.card E = r) (hperm : Permutes E (U : Subgroup K)) :
    E ≤ normalizer ((U : Subgroup K) : Set K) ∨ ∃ k : ℕ, r = 2 ^ k + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hY : E ⊔ (U : Subgroup K) ≤ normalizer ((U : Subgroup K) : Set K)
  · exact Or.inl (le_sup_left.trans hY)
  · right
    obtain ⟨k, hk1, hdvd⟩ := uc22p20k_div_of_splitBN hBN U (E ⊔ U) le_sup_right hY
    obtain ⟨a, ha⟩ := U.isPGroup'.exists_card_eq
    have hcop : Nat.Coprime r (2 ^ a) :=
      ((Nat.coprime_primes hr Nat.prime_two).2 hr2).pow_right a
    have hEU : E ⊓ (U : Subgroup K) = ⊥ :=
      Subgroup.inf_eq_bot_of_coprime (by rw [hcard, ha]; exact hcop)
    rw [CFSG.Quasithin.H.Tri.card_sup_eq_mul hperm hEU, hcard, ha] at hdvd
    have hodd : Nat.Coprime (2 ^ k + 1) (2 ^ a) := by
      refine Nat.Coprime.pow_right a (Nat.Coprime.symm ?_)
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      intro h
      have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
      omega
    rcases (Nat.dvd_prime hr).1 (hodd.dvd_of_dvd_mul_right hdvd) with h | h
    · have : 0 < 2 ^ k := by positivity
      omega
    · exact ⟨k, h.symm⟩

theorem not_dvd_card_of_lieModel_tits
    {K : Type} [Group K] {n f : ℕ}
    (hmod : CFSG.Blueprint.LieModel K .Tits n 2 f) {r : ℕ} (hr : r.Prime) (hr7 : 7 ≤ r)
    (hr13 : r ≠ 13) : ¬ r ∣ Nat.card K := by
  obtain ⟨-, hR⟩ := hmod.reeTitsModel (by decide)
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv K 2 f hR
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD,
    show (17971200 : ℕ) = 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13 by norm_num]
  intro h
  rcases (Nat.Prime.dvd_mul hr).1 h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hr).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hr).1 h2 with h3 | h3
      · have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h3)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 (hr.dvd_of_dvd_pow h3)
        omega
    · have := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 (hr.dvd_of_dvd_pow h2)
      omega
  · have := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h1
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
