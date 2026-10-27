module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102TorusFixAbstract
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102TorusFixU4Aut
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3U4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {n : ℕ} {K : Type} [Field K]

theorem torusFixConcl_hypSU_two_zero (h : UnitaryFieldData 2 n K) (hn : Even n) :
    TorusFixConcl (hypSU h 2 0) n := by
  have hn0 : n ≠ 0 := by
    have := h.one_le
    omega
  obtain ⟨q, m, b, hq, hqn, hm3, hnm, hqm⟩ :=
    exists_prime_dvd_two_pow_add_one_and_two_pow_sub_one hn0
  obtain ⟨σ, hσ, -, -, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality h.prime (n := 2 * n) (by omega) h.card
  let Φ : MulAut (hypSU h 2 0) := ASVolI.burnsideF4m_U4_fieldAut h σ
  let φ : MulAut (hypSU h 2 0) := Φ ^ m
  let S₀ : Subgroup (hypSU h 2 0) := Syl3.torusPow h 2 0 (3 ^ (Nat.card Kˣ).factorization 3)
  obtain ⟨hS₀, hS₀i, -, -⟩ := Syl3.sylow_three_hypSU_two_zero h hn
  have hφ : ∃ k : ℕ, φ ^ (3 ^ k) = 1 := by
    refine ⟨b, ?_⟩
    change (Φ ^ m) ^ (3 ^ b) = 1
    rw [← pow_mul, mul_comm m (3 ^ b), ← hnm]
    exact burnsideF4m_U4_fieldAut_pow_two_mul_eq_one h hσ
  have hpow : ∀ j : ℕ, ∀ s ∈ S₀, (Φ ^ j) s ∈ S₀ := by
    intro j
    induction j with
    | zero =>
        intro s hs
        simpa using hs
    | succ j ih =>
        intro s hs
        rw [pow_succ, MulAut.mul_apply]
        exact ih (Φ s) (burnsideF4m_U4_fieldAut_mem_torusPow h hσ hs)
  have hΦ : ∀ α : MulAut (hypSU h 2 0), ∃ y : hypSU h 2 0, ∃ j : ℕ,
      α = MulAut.conj y * Φ ^ j :=
    exists_conj_mul_burnsideF4m_U4_fieldAut_pow h hσ
  have hφi : ¬ 3 ∣ ((MulAut.conj : hypSU h 2 0 →* MulAut (hypSU h 2 0)).range ⊔
      Subgroup.zpowers φ).index := by
    intro h3
    exact hm3 (h3.trans (CFSG.index_range_conj_sup_zpowers_pow_dvd hΦ m))
  let : Fact q.Prime := ⟨hq⟩
  have hqcard : q ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card]
    have hdvd : 2 ^ n + 1 ∣ 2 ^ (2 * n) - 1 := by
      have hpow2 : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by
        conv_rhs => rw [← pow_mul, Nat.mul_comm]
      have hsq : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
        simpa using Nat.sq_sub_sq (2 ^ n) 1
      rw [hpow2, hsq]
      exact dvd_mul_right _ _
    exact hqn.trans hdvd
  let : Finite K := h.finite
  obtain ⟨μ, hμ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) q hqcard
  have hμpow : μ ^ (2 ^ m - 1) = 1 := by
    refine orderOf_dvd_iff_pow_eq_one.mp ?_
    rw [hμ]
    exact hqm
  have hφx₀ : φ (torusFixElem h μ) = torusFixElem h μ := by
    change (Φ ^ m) (torusFixElem h μ) = torusFixElem h μ
    rw [burnsideF4m_U4_fieldAut_pow_torusFixElem h hσ m μ]
    congr 1
    rw [show μ ^ 2 ^ m = μ ^ (2 ^ m - 1) * μ by
      rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow], hμpow, one_mul]
  let : Finite (hypSU h 2 0) := finite_hypSU h
  refine torusFixConcl_of_torus (x₀ := torusFixElem h μ) hS₀ hS₀i hφ (hpow m) hφi hq hqn
    ?_ ?_ hφx₀
  · rw [orderOf_torusFixElem, hμ]
  · intro s hs
    exact torusFixElem_mul_comm_of_mem_torusPow h μ hs

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
