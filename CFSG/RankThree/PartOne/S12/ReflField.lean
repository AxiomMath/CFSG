module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.RankThree.PartOne

namespace ReflF

section Basic

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

structure ReflData (T : V ≃ₗ[K] V) (r : V) (φ : V →ₗ[K] K) : Prop where
  ne : r ≠ 0
  pair : φ r = 2
  apply : ∀ x, T x = x - φ x • r

theorem ReflData.apply_root {T : V ≃ₗ[K] V} {r : V} {φ : V →ₗ[K] K} (h : ReflData T r φ) :
    T r = -r := by
  rw [h.apply r, h.pair]
  module

theorem ReflData.mul_self {T : V ≃ₗ[K] V} {r : V} {φ : V →ₗ[K] K} (h : ReflData T r φ) :
    T * T = 1 := by
  ext x
  have h1 : T (T x) = T x - φ x • T r := by
    have := congrArg T (h.apply x)
    rw [this, map_sub, map_smul]
  show T (T x) = x
  rw [h1, h.apply_root, h.apply x]
  module

theorem ReflData.conj {T : V ≃ₗ[K] V} {r : V} {φ : V →ₗ[K] K} (h : ReflData T r φ)
    (g : V ≃ₗ[K] V) :
    ReflData (g * T * g⁻¹) (g r) (φ ∘ₗ (g.symm : V →ₗ[K] V)) where
  ne := fun h0 => h.ne (g.injective (by rw [h0, map_zero]))
  pair := by
    simp [h.pair]
  apply x := by
    have hg : (g⁻¹ : V ≃ₗ[K] V) x = g.symm x := rfl
    show g (T (g⁻¹ x)) = x - φ (g.symm x) • g r
    rw [hg, h.apply, map_sub, map_smul, LinearEquiv.apply_symm_apply]

theorem ReflData.mul_apply {T T' : V ≃ₗ[K] V} {r r' : V} {φ φ' : V →ₗ[K] K}
    (h : ReflData T r φ) (h' : ReflData T' r' φ') (x : V) :
    (T * T') x = x - φ' x • r' - φ x • r + (φ r' * φ' x) • r := by
  show T (T' x) = _
  rw [h'.apply x, h.apply, map_sub, map_smul]
  module

theorem ReflData.neg {T : V ≃ₗ[K] V} {r : V} {φ : V →ₗ[K] K} (h : ReflData T r φ) :
    ReflData T (-r) (-φ) where
  ne := fun h0 => h.ne (neg_eq_zero.1 h0)
  pair := by
    simp [h.pair]
  apply x := by
    rw [h.apply x]
    simp

theorem ReflData.rescale {T : V ≃ₗ[K] V} {r : V} {φ : V →ₗ[K] K} (h : ReflData T r φ)
    {c μ : K} (hcμ : c * μ = 1) : ReflData T (μ • r) (c • φ) where
  ne := by
    intro h0
    have h1 : μ = 0 := (smul_eq_zero.1 h0).resolve_right h.ne
    rw [h1, mul_zero] at hcμ
    exact zero_ne_one hcμ
  pair := by
    rw [LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, h.pair]
    linear_combination 2 * hcμ
  apply x := by
    rw [h.apply x, LinearMap.smul_apply, smul_eq_mul, smul_smul]
    have : c * φ x * μ = φ x := by linear_combination (φ x) * hcμ
    rw [this]

end Basic

section Pairs

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def step (a b : K) (z : K × K) : K × K :=
  ((a * b - 1) * z.1 + a * z.2, -b * z.1 - z.2)

theorem step_two (h2 : (2 : K) ≠ 0) (a b : K) (h1 : (step a b)^[2] (1, 0) = (1, 0))
    (h2' : (step a b)^[2] (0, 1) = (0, 1)) : a = 0 ∧ b = 0 := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, step,
    Prod.mk.injEq] at h1 h2'
  obtain ⟨-, e1⟩ := h1
  obtain ⟨e2, e3⟩ := h2'
  have hab : a * b = 0 := by linear_combination -e3
  have ha : a * 2 = 0 := by linear_combination -e2 + a * hab
  have hb : b * 2 = 0 := by linear_combination e1 + b * hab
  exact ⟨(mul_eq_zero.1 ha).resolve_right h2, (mul_eq_zero.1 hb).resolve_right h2⟩

theorem step_three (h2 : (2 : K) ≠ 0) (a b : K) (h1 : (step a b)^[3] (1, 0) = (1, 0))
    (h2' : (step a b)^[3] (0, 1) = (0, 1)) : a * b = 1 := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, step,
    Prod.mk.injEq] at h1 h2'
  obtain ⟨-, e1⟩ := h1
  obtain ⟨e2, e3⟩ := h2'
  have ht : (a * b - 1) * (a * b - 2) = 0 := by linear_combination -e3
  rcases mul_eq_zero.1 ht with h | h
  · linear_combination h
  · exfalso
    have hab : a * b = 2 := by linear_combination h
    have ha : a = 0 := by
      have h3 : a * ((a * b - 3) * (a * b - 1)) = 0 := by linear_combination e2
      rw [hab] at h3
      linear_combination -h3
    have hb : b = 0 := by
      have h3 : b * ((a * b - 3) * (a * b - 1)) = 0 := by linear_combination -e1
      rw [hab] at h3
      linear_combination -h3
    exact h2 (by rw [← hab, ha, zero_mul])

theorem refl_pair (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {T T' : V ≃ₗ[K] V} {r r' : V}
    {φ φ' : V →ₗ[K] K} (h : ReflData T r φ) (h' : ReflData T' r' φ') (hne : T ≠ T') :
    ((T * T') ^ 2 = 1 → φ r' = 0 ∧ φ' r = 0) ∧ ((T * T') ^ 3 = 1 → φ r' * φ' r = 1) := by
  have hU1 : T * T' ≠ 1 := by
    intro h1
    apply hne
    calc T = T * (T * T') := by rw [h1, mul_one]
      _ = T' := by rw [← mul_assoc, h.mul_self, one_mul]
  by_cases hdep : ∃ l : K, r' = l • r
  ·
    obtain ⟨l, hl⟩ := hdep
    let ψ : V →ₗ[K] K := φ - l • φ'
    have hψr : ψ r = 0 := by
      have h2' : φ' r' = 2 := h'.pair
      rw [hl, map_smul, smul_eq_mul] at h2'
      show φ r - l * φ' r = 0
      rw [h.pair]
      linear_combination -h2'
    have hU : ∀ x, (T * T') x = x - ψ x • r := by
      intro x
      have hφr' : φ r' = 2 * l := by
        rw [hl, map_smul, smul_eq_mul, h.pair, mul_comm]
      rw [h.mul_apply h' x, hφr', hl]
      show _ = x - (φ x - l * φ' x) • r
      module
    have hpow : ∀ k : ℕ, ∀ x, ((T * T') ^ k) x = x - ((k : K) * ψ x) • r := by
      intro k
      induction k with
      | zero =>
        intro x
        simp
      | succ k ih =>
        intro x
        rw [pow_succ', LinearEquiv.mul_apply, ih x, hU, map_sub, map_smul, hψr]
        simp only [smul_eq_mul, mul_zero, sub_zero, Nat.cast_succ]
        module
    have hk : ∀ k : ℕ, (T * T') ^ k = 1 → (k : K) ≠ 0 → T * T' = 1 := by
      intro k hk1 hk0
      have hx : ∀ x, ψ x = 0 := by
        intro x
        have h1 : x = x - ((k : K) * ψ x) • r := by
          have := hpow k x
          rw [hk1] at this
          exact this
        have h2'' : ((k : K) * ψ x) • r = 0 := by
          have h3' : x - x = x - (x - ((k : K) * ψ x) • r) := by
            rw [← h1]
          simpa using h3'.symm
        have h3' := (smul_eq_zero.1 h2'').resolve_right h.ne
        exact (mul_eq_zero.1 h3').resolve_left hk0
      ext x
      rw [hU x, hx x, zero_smul, sub_zero]
      rfl
    exact ⟨fun h2' => absurd (hk 2 h2' (by exact_mod_cast h2)) hU1,
      fun h3' => absurd (hk 3 h3' (by exact_mod_cast h3)) hU1⟩
  ·
    have hind : ∀ s t : K, s • r + t • r' = 0 → s = 0 ∧ t = 0 := by
      intro s t hst
      by_cases ht : t = 0
      · subst ht
        rw [zero_smul, add_zero] at hst
        exact ⟨(smul_eq_zero.1 hst).resolve_right h.ne, rfl⟩
      · exfalso
        apply hdep
        refine ⟨-(t⁻¹ * s), ?_⟩
        have h1 : t • r' = -(s • r) := eq_neg_of_add_eq_zero_right hst
        have h2' : r' = t⁻¹ • (-(s • r)) := by
          rw [← h1, smul_smul, inv_mul_cancel₀ ht, one_smul]
        rw [h2']
        module
    set a := φ r' with ha
    set b := φ' r with hb
    have hUr : (T * T') r = (a * b - 1) • r + (-b) • r' := by
      rw [h.mul_apply h' r, h.pair]
      module
    have hUr' : (T * T') r' = a • r + (-1 : K) • r' := by
      rw [h.mul_apply h' r', h'.pair]
      module
    have hstep : ∀ x y : K, (T * T') (x • r + y • r') =
        (step a b (x, y)).1 • r + (step a b (x, y)).2 • r' := by
      intro x y
      rw [map_add, map_smul, map_smul, hUr, hUr']
      simp only [step]
      module
    have hpow : ∀ k : ℕ, ∀ x y : K, ((T * T') ^ k) (x • r + y • r') =
        ((step a b)^[k] (x, y)).1 • r + ((step a b)^[k] (x, y)).2 • r' := by
      intro k
      induction k with
      | zero =>
        intro x y
        simp
      | succ k ih =>
        intro x y
        rw [pow_succ', LinearEquiv.mul_apply, ih, hstep, ← Function.iterate_succ_apply' (step a b)]
    have hcoef : ∀ k : ℕ, (T * T') ^ k = 1 → (step a b)^[k] (1, 0) = (1, 0) ∧
        (step a b)^[k] (0, 1) = (0, 1) := by
      intro k hk1
      have e1 := hpow k 1 0
      have e2 := hpow k 0 1
      rw [hk1] at e1 e2
      have e1' : r = ((step a b)^[k] (1, 0)).1 • r + ((step a b)^[k] (1, 0)).2 • r' := by
        have := e1
        simpa using this
      have e2' : r' = ((step a b)^[k] (0, 1)).1 • r + ((step a b)^[k] (0, 1)).2 • r' := by
        have := e2
        simpa using this
      constructor
      · have := hind (((step a b)^[k] (1, 0)).1 - 1) ((step a b)^[k] (1, 0)).2 (by
          calc _ = (((step a b)^[k] (1, 0)).1 • r + ((step a b)^[k] (1, 0)).2 • r') - r := by
                module
            _ = 0 := by rw [← e1']; exact sub_self r)
        exact Prod.ext (sub_eq_zero.1 this.1) this.2
      · have := hind ((step a b)^[k] (0, 1)).1 (((step a b)^[k] (0, 1)).2 - 1) (by
          calc _ = (((step a b)^[k] (0, 1)).1 • r + ((step a b)^[k] (0, 1)).2 • r') - r' := by
                module
            _ = 0 := by rw [← e2']; exact sub_self r')
        exact Prod.ext this.1 (sub_eq_zero.1 this.2)
    refine ⟨fun h2' => ?_, fun h3' => ?_⟩
    · obtain ⟨c1, c2⟩ := hcoef 2 h2'
      exact step_two h2 a b c1 c2
    · obtain ⟨c1, c2⟩ := hcoef 3 h3'
      exact step_three h2 a b c1 c2

theorem dichotomy (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {T T' : V ≃ₗ[K] V} {r r' : V}
    {φ φ' : V →ₗ[K] K} (h : ReflData T r φ) (h' : ReflData T' r' φ') (hne : T ≠ T')
    (hord : (T * T') ^ 1 = 1 ∨ (T * T') ^ 2 = 1 ∨ (T * T') ^ 3 = 1) :
    (φ r' = 0 ∧ φ' r = 0) ∨ φ r' * φ' r = 1 := by
  have hU1 : T * T' ≠ 1 := by
    intro h1
    apply hne
    calc T = T * (T * T') := by rw [h1, mul_one]
      _ = T' := by rw [← mul_assoc, h.mul_self, one_mul]
  obtain ⟨e2, e3⟩ := refl_pair h2 h3 h h' hne
  rcases hord with h1 | h4 | h5
  · exact absurd (by simpa using h1) hU1
  · exact Or.inl (e2 h4)
  · exact Or.inr (e3 h5)

theorem commute_orth (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {T T' : V ≃ₗ[K] V} {r r' : V}
    {φ φ' : V →ₗ[K] K} (h : ReflData T r φ) (h' : ReflData T' r' φ') (hne : T ≠ T')
    (hc : T * T' = T' * T) : φ r' = 0 ∧ φ' r = 0 := by
  refine (refl_pair h2 h3 h h' hne).1 ?_
  have hcomm : Commute T T' := hc
  rw [hcomm.mul_pow, pow_two T, h.mul_self, pow_two T', h'.mul_self, one_mul]

theorem commute_of_orth {T T' : V ≃ₗ[K] V} {r r' : V} {φ φ' : V →ₗ[K] K}
    (h : ReflData T r φ) (h' : ReflData T' r' φ') (h1 : φ r' = 0) (h2 : φ' r = 0) :
    T * T' = T' * T := by
  ext x
  show (T * T') x = (T' * T) x
  rw [h.mul_apply h' x, h'.mul_apply h x, h1, h2]
  simp only [zero_mul, zero_smul, add_zero]
  abel

theorem not_orth_of_not_commute {T T' : V ≃ₗ[K] V} {r r' : V} {φ φ' : V →ₗ[K] K}
    (h : ReflData T r φ) (h' : ReflData T' r' φ') (hc : T * T' ≠ T' * T) :
    ¬ (φ r' = 0 ∧ φ' r = 0) := fun ⟨h1, h2⟩ => hc (commute_of_orth h h' h1 h2)

end Pairs

end ReflF

end CFSG.RankThree.PartOne
