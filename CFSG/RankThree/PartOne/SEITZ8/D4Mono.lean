module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

public section

namespace CFSG.RankThree.PartOne.SEITZ8

open Polynomial

@[expose] def MonoInd (L : Type*) [Field L] (σL : L →+* L) : Prop :=
  ∀ c : ℕ × ℕ × ℕ → L,
    (∀ a : L, ∑ m ∈ Finset.range 2 ×ˢ Finset.range 2 ×ˢ Finset.range 2,
      c m * (σL (σL a) ^ m.1 * σL a ^ m.2.1 * a ^ m.2.2) = 0) →
    ∀ m ∈ Finset.range 2 ×ˢ Finset.range 2 ×ˢ Finset.range 2, c m = 0

theorem digits_inj {q : ℕ} (hq : 2 ≤ q) {a b c a' b' c' : ℕ} (ha : a ≤ 1) (hb : b ≤ 1)
    (hc : c ≤ 1) (ha' : a' ≤ 1) (hb' : b' ≤ 1) (hc' : c' ≤ 1)
    (h : a * q ^ 2 + b * q + c = a' * q ^ 2 + b' * q + c') : a = a' ∧ b = b' ∧ c = c' := by
  have hq2 : 4 ≤ q ^ 2 := by nlinarith
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases a' <;>
    interval_cases b' <;> interval_cases c' <;> first | exact ⟨rfl, rfl, rfl⟩ | (exfalso; nlinarith)

theorem monoInd_of_weights {L : Type*} [Field L] [Fintype L] (σL : L →+* L) {q : ℕ} (hq : 2 ≤ q)
    (hL : Fintype.card L = q ^ 3) {w₃ w₁ : ℕ} (hw : (w₃ = q ^ 2 ∧ w₁ = q) ∨ (w₃ = q ∧ w₁ = q ^ 2))
    (h₃ : ∀ a, σL (σL a) = a ^ w₃) (h₁ : ∀ a, σL a = a ^ w₁) : MonoInd L σL := by
  classical
  intro c hc m hm
  set e : ℕ × ℕ × ℕ → ℕ := fun m => m.1 * w₃ + m.2.1 * w₁ + m.2.2 with he
  have hχ : ∀ (a : L) (m : ℕ × ℕ × ℕ), σL (σL a) ^ m.1 * σL a ^ m.2.1 * a ^ m.2.2 = a ^ e m := by
    intro a m
    rw [h₃, h₁, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    congr 1
    simp only [he]
    ring
  have hinj : ∀ m ∈ Finset.range 2 ×ˢ Finset.range 2 ×ˢ Finset.range 2,
      ∀ m' ∈ Finset.range 2 ×ˢ Finset.range 2 ×ˢ Finset.range 2, e m = e m' → m = m' := by
    intro m hm m' hm' hmm
    simp only [Finset.mem_product, Finset.mem_range] at hm hm'
    obtain ⟨hm1, hm2, hm3⟩ := hm
    obtain ⟨hm1', hm2', hm3'⟩ := hm'
    simp only [he] at hmm
    rcases hw with ⟨h3, h1⟩ | ⟨h3, h1⟩
    · rw [h3, h1] at hmm
      obtain ⟨e1, e2, e3⟩ := digits_inj hq (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) hmm
      exact Prod.ext e1 (Prod.ext e2 e3)
    · rw [h3, h1] at hmm
      obtain ⟨e1, e2, e3⟩ := digits_inj hq (a := m.2.1) (b := m.1) (c := m.2.2)
        (a' := m'.2.1) (b' := m'.1) (c' := m'.2.2) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by linarith)
      exact Prod.ext e2 (Prod.ext e1 e3)
  set P : L[X] := ∑ m' ∈ Finset.range 2 ×ˢ Finset.range 2 ×ˢ Finset.range 2,
    C (c m') * X ^ e m' with hP
  have hemax : ∀ m' ∈ Finset.range 2 ×ˢ Finset.range 2 ×ˢ Finset.range 2, e m' < q ^ 3 := by
    intro m' hm'
    simp only [Finset.mem_product, Finset.mem_range] at hm'
    obtain ⟨h1, h2, h3⟩ := hm'
    simp only [he]
    have hq3 : q ^ 3 = q * q * q := by ring
    have hs : m'.1 * w₃ + m'.2.1 * w₁ + m'.2.2 ≤ q ^ 2 + q + 1 := by
      rcases hw with ⟨h3, h1⟩ | ⟨h3, h1⟩
      · rw [h3, h1]
        nlinarith [Nat.zero_le (m'.1 * q ^ 2)]
      · rw [h3, h1]
        nlinarith
    nlinarith
  have hdeg : P.natDegree < (Finset.univ : Finset L).card := by
    rw [Finset.card_univ, hL]
    refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _
      (n := q ^ 3 - 1) fun m' hm' => ?_) ?_
    · refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
      have := hemax m' hm'
      omega
    · have : 0 < q ^ 3 := by positivity
      omega
  have hzero : P = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P (Finset.univ : Finset L)
      (fun a _ => ?_) hdeg
    rw [hP, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    have := hc a
    rw [← this]
    refine Finset.sum_congr rfl fun m' _ => ?_
    rw [hχ]
  have hcoeff := congrArg (fun p : L[X] => p.coeff (e m)) hzero
  simp only [hP, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single m] at hcoeff
  · simpa using hcoeff
  · intro m' hm' hne
    exact ite_eq_right (fun hee => hne (hinj m hm m' hm' hee).symm)
  · intro hnm
    exact absurd hm hnm

theorem monoInd_of_frobenius {L : Type*} [Field L] [Fintype L] (σL : L →+* L) {q : ℕ}
    (hq : 2 ≤ q) (hL : Fintype.card L = q ^ 3) {j : ℕ} (hj : j = 1 ∨ j = 2)
    (hσ : ∀ a, σL a = a ^ q ^ j) : MonoInd L σL := by
  have hpow : ∀ a : L, a ^ q ^ 3 = a := fun a => by
    have := FiniteField.pow_card a
    rwa [hL] at this
  rcases hj with rfl | rfl
  · refine monoInd_of_weights σL hq hL (w₃ := q ^ 2) (w₁ := q) (Or.inl ⟨rfl, rfl⟩) ?_ ?_
    · intro a
      rw [hσ, hσ, ← pow_mul]
      congr 1
      ring
    · intro a
      rw [hσ, pow_one]
  · refine monoInd_of_weights σL hq hL (w₃ := q) (w₁ := q ^ 2) (Or.inr ⟨rfl, rfl⟩) ?_ ?_
    · intro a
      rw [hσ, hσ, ← pow_mul]
      have : q ^ 2 * q ^ 2 = q ^ 3 * q := by ring
      rw [this, pow_mul, hpow]
    · intro a
      rw [hσ]

theorem extract8 {L : Type*} [Field L] {σL : L →+* L} (hind : MonoInd L σL) {V : Type*}
    [AddCommGroup V] [Module L V] (W : Submodule L V) (u : ℕ × ℕ × ℕ → V)
    (h : ∀ a : L, ∑ m ∈ Finset.range 2 ×ˢ Finset.range 2 ×ˢ Finset.range 2,
      (σL (σL a) ^ m.1 * σL a ^ m.2.1 * a ^ m.2.2) • u m ∈ W) :
    ∀ m ∈ Finset.range 2 ×ˢ Finset.range 2 ×ˢ Finset.range 2, u m ∈ W := by
  intro m hm
  by_contra hmW
  have hne : W.mkQ (u m) ≠ 0 := by
    rw [Submodule.mkQ_apply]
    exact fun h0 => hmW ((Submodule.Quotient.mk_eq_zero W).1 h0)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero L hne
  have key : ∀ m' ∈ Finset.range 2 ×ˢ Finset.range 2 ×ˢ Finset.range 2,
      φ (W.mkQ (u m')) = 0 := by
    refine hind (fun m' => φ (W.mkQ (u m'))) (fun a => ?_)
    have h1 := h a
    have h2 : φ (W.mkQ (∑ m ∈ Finset.range 2 ×ˢ Finset.range 2 ×ˢ Finset.range 2,
      (σL (σL a) ^ m.1 * σL a ^ m.2.1 * a ^ m.2.2) • u m)) = 0 := by
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).2 h1, map_zero]
    simp only [map_sum, map_smul, smul_eq_mul] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun m' _ => ?_
    rw [mul_comm]
  exact hφ (key m hm)

end CFSG.RankThree.PartOne.SEITZ8
