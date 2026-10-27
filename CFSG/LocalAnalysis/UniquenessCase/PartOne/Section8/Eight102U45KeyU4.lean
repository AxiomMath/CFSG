module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102U45KeyAbstract
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102U45KeyU4Torus
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102U45KeyU4Out
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3U4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {n : ℕ} {K : Type} [Field K]

theorem u45KeyConcl_hypSU_two_zero (h : UnitaryFieldData 2 n K) (hn : Even n)
    (hX : UC22.IsU4 (hypSU h 2 0) n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hpn : ¬ p ∣ 2 ^ n + 1) : U45KeyConcl (hypSU h 2 0) p := by
  obtain ⟨σ, hσ, -, -, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality h.prime (n := 2 * n)
      (by have := h.one_le; omega) h.card
  let Φ : MulAut (hypSU h 2 0) := ASVolI.burnsideF4m_U4_fieldAut h σ
  have hΦ : ∀ α : MulAut (hypSU h 2 0), ∃ y : hypSU h 2 0, ∃ j : ℕ,
      α = MulAut.conj y * Φ ^ j := exists_conj_mul_burnsideF4m_U4_fieldAut_pow h hσ
  have hΦpow : Φ ^ (2 * n) = 1 := burnsideF4m_U4_fieldAut_pow_two_mul_eq_one h hσ
  have h2n : 2 * n ≠ 0 := by
    have := h.one_le
    omega
  obtain ⟨a, m, hpm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd h2n p hp.ne_one
  have hΦm : Φ ^ (p ^ a * m) = 1 := hnm ▸ hΦpow
  let S₀ : Subgroup (hypSU h 2 0) := Syl3.torusPow h 2 0 (3 ^ (Nat.card Kˣ).factorization 3)
  obtain ⟨hS₀, hS₀i, -, -⟩ := Syl3.sylow_three_hypSU_two_zero h hn
  have hΦS : ∀ s ∈ S₀, (Φ ^ m) s = s := fun s hs =>
    burnsideF4m_U4_fieldAut_pow_apply_of_mem_torusPow h hσ
      (three_pow_factorization_dvd_two_pow_sub_one h hp hp2 hp3 hnm) hs
  have : Fact p.Prime := ⟨hp⟩
  let : Finite (hypSU h 2 0) := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  by_cases hp' : p ∣ 2 ^ n - 1
  · let P₀ : Subgroup (hypSU h 2 0) :=
      Syl3.torusPow h 2 0 (p ^ (Nat.card Kˣ).factorization p)
    obtain ⟨hP₀, hP₀i⟩ := sylow_torusPow_hypSU_two_zero h hp hp2 hp'
    have hpow : ∀ j : ℕ, ∀ s ∈ P₀, (Φ ^ j) s ∈ P₀ := by
      intro j
      induction j with
      | zero =>
          intro s hs
          simpa using hs
      | succ j ih =>
          intro s hs
          rw [pow_succ, MulAut.mul_apply]
          exact ih (Φ s) (burnsideF4m_U4_fieldAut_mem_torusPow h hσ hs)
    have hΦP : ∀ s ∈ P₀, (Φ ^ m) s ∈ P₀ := hpow m
    have hPS : ∀ x ∈ P₀, ∀ s ∈ S₀, x * s = s * x := fun x hx s hs =>
      mul_comm_of_mem_torusPow hx hs
    exact u45KeyConcl_of_torus (a := a) (m := m) (P₀ := P₀) (S₀ := S₀) hΦ hpm hΦm hP₀
      hP₀i hΦP hS₀ hS₀i hPS hΦS
  · refine u45KeyConcl_of_cyclic (m := m) (a := a) (S₀ := S₀) hp2
      (conj_injective_of_isU4 hX) hΦ ?_ hpm hΦm
      (pRank_le_one_of_isU4 hX hp hp2 hpn hp') hS₀ hS₀i hΦS
    intro k hk
    exact burnsideF4m_U4_fieldAut_pow_eq_one_of_mem_range h hX hσ hk

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
