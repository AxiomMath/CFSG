module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndAutThreeOrders
import CFSG.Adapters.LieModelOrders
import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart
import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoUThree
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKillAux
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Blueprint (LieModel)
open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private lemma factorization_three_sq_mul_of_not_dvd {m : ℕ} (hm : ¬ 3 ∣ m) :
    (3 ^ 2 * m).factorization 3 = 2 := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by norm_num)
  rw [Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul,
    Nat.Prime.factorization_self Nat.prime_three,
    Nat.factorization_eq_zero_of_not_dvd hm]
  norm_num

theorem factorization_three_card_ne_three_of_isAlt {L : Type} [Group L]
    (h : UC22.IsAlt L 7 ∨ UC22.IsAlt L 6) : (Nat.card L).factorization 3 ≠ 3 := by
  haveI : Nontrivial (Fin 7) := Fin.nontrivial_iff_two_le.2 (by norm_num)
  haveI : Nontrivial (Fin 6) := Fin.nontrivial_iff_two_le.2 (by norm_num)
  rcases h with h | h
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin,
      show (Nat.factorial 7 / 2 : ℕ) = 3 ^ 2 * 280 by norm_num,
      factorization_three_sq_mul_of_not_dvd (by norm_num : ¬ 3 ∣ 280)]
    norm_num
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin,
      show (Nat.factorial 6 / 2 : ℕ) = 3 ^ 2 * 40 by norm_num,
      factorization_three_sq_mul_of_not_dvd (by norm_num : ¬ 3 ∣ 40)]
    norm_num

private lemma factorization_three_psl_three {L : Type} [Group L] {p f : ℕ}
    (h : LieModel L .PSL 3 p f) (hq : p ^ f % 3 = 1) :
    (Nat.card L).factorization 3 ≠ 3 := by
  have hcard : Nat.card L = ordA 2 (p ^ f) := h.card_eq_lieOrd (by norm_num)
  rw [hcard, factorization_three_ordA_two hq]
  omega

private lemma factorization_three_psu_three {L : Type} [Group L] {p f : ℕ}
    (h : LieModel L .PSU 3 p f) (hq : p ^ f % 3 = 2) :
    (Nat.card L).factorization 3 ≠ 3 := by
  have hcard : Nat.card L = ordTwistedA 2 (p ^ f) := h.card_eq_lieOrd (by norm_num)
  rw [hcard, factorization_three_ordTwistedA_two hq]
  omega

private lemma factorization_three_psp_two {L : Type} [Group L] {p f : ℕ}
    (h : LieModel L .PSp 2 p f) : (Nat.card L).factorization 3 ≠ 3 := by
  have hcard : Nat.card L = ordBC 2 (p ^ f) := h.card_eq_lieOrd (by norm_num)
  by_cases h3 : 3 ∣ p ^ f
  · have h81 : 81 ∣ Nat.card L := by
      rw [hcard]
      exact eightyone_dvd_ordBC_two h3
    rcases eq_or_ne (Nat.card L) 0 with h0 | h0
    · simp [h0]
    · have h81' : 3 ^ 4 ∣ Nat.card L := by
        simpa only [show (3 : ℕ) ^ 4 = 81 by norm_num] using h81
      have h4 : 4 ≤ (Nat.card L).factorization 3 :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three h0).mp h81'
      omega
  · rw [hcard, factorization_three_ordBC_two h3]
    omega

private lemma factorization_three_psl_four {L : Type} [Group L] {p f : ℕ}
    (h : LieModel L .PSL 4 p f) (hq : p ^ f % 3 = 2) :
    (Nat.card L).factorization 3 ≠ 3 := by
  have hcard : Nat.card L = ordA 3 (p ^ f) := h.card_eq_lieOrd (by norm_num)
  rw [hcard, factorization_three_ordA_three hq]
  omega

private lemma factorization_three_psu_four {L : Type} [Group L] {p f : ℕ}
    (h : LieModel L .PSU 4 p f) (hq : p ^ f % 3 = 1) :
    (Nat.card L).factorization 3 ≠ 3 := by
  have hcard : Nat.card L = ordTwistedA 3 (p ^ f) := h.card_eq_lieOrd (by norm_num)
  rw [hcard, factorization_three_ordTwistedA_three hq]
  omega

private lemma factorization_three_psl_five {L : Type} [Group L] {p f : ℕ}
    (h : LieModel L .PSL 5 p f) (hq : p ^ f % 3 = 2) :
    (Nat.card L).factorization 3 ≠ 3 := by
  have hcard : Nat.card L = ordA 4 (p ^ f) := h.card_eq_lieOrd (by norm_num)
  rw [hcard, factorization_three_ordA_four hq]
  omega

private lemma factorization_three_psu_five {L : Type} [Group L] {p f : ℕ}
    (h : LieModel L .PSU 5 p f) (hq : p ^ f % 3 = 1) :
    (Nat.card L).factorization 3 ≠ 3 := by
  have hcard : Nat.card L = ordTwistedA 4 (p ^ f) := h.card_eq_lieOrd (by norm_num)
  rw [hcard, factorization_three_ordTwistedA_four hq]
  omega

theorem factorization_three_card_ne_three_of_k33_classical {L : Type} [Group L]
    (h : (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel L .PSL 3 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel L .PSU 3 p f) ∨ (∃ p f : ℕ, LieModel L .PSp 2 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel L .PSL 4 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel L .PSU 4 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel L .PSL 5 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel L .PSU 5 p f)) :
    (Nat.card L).factorization 3 ≠ 3 := by
  rcases h with ⟨p, f, hq, h⟩ | ⟨p, f, hq, h⟩ | ⟨p, f, h⟩ | ⟨p, f, hq, h⟩ |
    ⟨p, f, hq, h⟩ | ⟨p, f, hq, h⟩ | ⟨p, f, hq, h⟩
  · exact factorization_three_psl_three h hq
  · exact factorization_three_psu_three h hq
  · exact factorization_three_psp_two h
  · exact factorization_three_psl_four h hq
  · exact factorization_three_psu_four h hq
  · exact factorization_three_psl_five h hq
  · exact factorization_three_psu_five h hq

theorem exists_eq_conj_of_lieModel_psl_three_three {L : Type} [Group L] [Finite L]
    (h : LieModel L .PSL 3 3 1) (φ : MulAut L) (hφ : ∃ n : ℕ, φ ^ (3 ^ n) = 1) :
    ∃ k : L, φ = MulAut.conj k := by
  have hclass : StatedClassicalModel L .PSL 3 3 1 := h.statedClassicalModel (by decide)
  have hdvd : Nat.card (Outer L) ∣ 2 := by
    have hd := (CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound L 3 3 1
      hclass).2.2.2.2 (by norm_num)
    simpa using hd
  have hOut : ¬ 3 ∣ Nat.card (Outer L) := by
    intro h3
    exact absurd (h3.trans hdvd) (by norm_num)
  haveI : Finite (MulAut L) :=
    Finite.of_injective (fun f : MulAut L => (f : L → L)) DFunLike.coe_injective
  haveI : Finite (Outer L) := Quotient.finite _
  obtain ⟨n, hn⟩ := hφ
  have hinner := CFSG.AGLEmbedding.mem_inner_of_pow_prime_pow_eq_one
    (K := L) Nat.prime_three hOut (f := φ) hn
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.1
    (show φ ∈ (MulAut.conj : L →* MulAut L).range from hinner)
  exact ⟨k, hk.symm⟩

theorem exists_eq_conj_of_lieModel_psu_three_three {L : Type} [Group L] [Finite L]
    (h : LieModel L .PSU 3 3 1) (φ : MulAut L) (hφ : ∃ n : ℕ, φ ^ (3 ^ n) = 1) :
    ∃ k : L, φ = MulAut.conj k := by
  have hclass : StatedClassicalModel L .PSU 3 3 1 := h.statedClassicalModel (by decide)
  have hOut : ¬ 3 ∣ Nat.card (Outer L) := by
    rw [CFSG.AGLEmbedding.card_outer_eq_two_of_model_psu_three_three hclass]
    norm_num
  haveI : Finite (MulAut L) :=
    Finite.of_injective (fun f : MulAut L => (f : L → L)) DFunLike.coe_injective
  haveI : Finite (Outer L) := Quotient.finite _
  obtain ⟨n, hn⟩ := hφ
  have hinner := CFSG.AGLEmbedding.mem_inner_of_pow_prime_pow_eq_one
    (K := L) Nat.prime_three hOut (f := φ) hn
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.1
    (show φ ∈ (MulAut.conj : L →* MulAut L).range from hinner)
  exact ⟨k, hk.symm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
