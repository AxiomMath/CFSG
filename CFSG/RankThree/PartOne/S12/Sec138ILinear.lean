module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.RankThree.PartOne

namespace Sec138I

theorem no_triangle :
    ∀ x y u v : ZMod 5, x * y = 1 → u * v = 1 → (u - x) * (v - y) = 1 → False := by
  decide

theorem sum_ne_zero : ∀ (S : Fin 5 → Bool) (u w : ZMod 5), u ≠ w →
    (∃ i, S i = true) → (∃ i, S i = false) →
    ∑ k : Fin 5, (if S k then u else w) ≠ 0 := by
  decide

theorem clique_five (c d : Fin 5 → ZMod 5) (hsum : ∑ k, c k = 0)
    (h : ∀ i j, i ≠ j → (c i = c j ∧ d i = d j) ∨ (c i - c j) * (d i - d j) = 1) :
    ∀ i j, c i = c j ∧ d i = d j := by
  classical
  have hprod : ∀ i j, ¬ (c i = c j ∧ d i = d j) → (c i - c j) * (d i - d j) = 1 := by
    intro i j hne
    by_cases hij : i = j
    · subst hij
      exact absurd ⟨rfl, rfl⟩ hne
    · exact (h i j hij).resolve_left hne
  have htri : ∀ i j k, ¬ (c i = c j ∧ d i = d j) → ¬ (c i = c k ∧ d i = d k) →
      (c j = c k ∧ d j = d k) := by
    intro i j k hij hik
    by_contra hjk
    have h1 := hprod i j hij
    have h2 := hprod i k hik
    have h3 := hprod j k hjk
    exact no_triangle (c j - c i) (d j - d i) (c k - c i) (d k - d i)
      (by linear_combination h1) (by linear_combination h2) (by linear_combination h3)
  by_contra hcon
  obtain ⟨i₀, hi₀⟩ := not_forall.1 hcon
  obtain ⟨j₀, hij⟩ := not_forall.1 hi₀
  have hex : ∃ b : Fin 5, ¬ (c 0 = c b ∧ d 0 = d b) := by
    by_contra hall
    have hall' : ∀ b : Fin 5, c 0 = c b ∧ d 0 = d b := fun b =>
      not_not.1 (not_exists.1 hall b)
    exact hij ⟨(hall' i₀).1.symm.trans (hall' j₀).1, (hall' i₀).2.symm.trans (hall' j₀).2⟩
  obtain ⟨b, hb⟩ := hex
  have hcover : ∀ k, (c 0 = c k ∧ d 0 = d k) ∨ (c b = c k ∧ d b = d k) := by
    intro k
    by_cases hk : c 0 = c k ∧ d 0 = d k
    · exact Or.inl hk
    · exact Or.inr (htri 0 b k hb hk)
  let S : Fin 5 → Bool := fun k => decide (c 0 = c k ∧ d 0 = d k)
  have hS0 : S 0 = true := by
    simp [S]
  have hSb : S b = false := by
    simpa [S] using hb
  have hcb : c 0 ≠ c b := by
    intro heq
    have h1 := hprod 0 b hb
    rw [heq, sub_self, zero_mul] at h1
    exact absurd h1 (by decide)
  have hfun : ∀ k, c k = if S k then c 0 else c b := by
    intro k
    rcases hcover k with hk | hk
    · have : S k = true := by simpa [S] using hk
      rw [this]
      simp [hk.1]
    · by_cases hSk : S k = true
      · have hk' : c 0 = c k ∧ d 0 = d k := by simpa [S] using hSk
        rw [hSk]
        simp [hk'.1]
      · have hSk' : S k = false := by simpa using hSk
        rw [hSk']
        simp [hk.1]
  have hsum' : ∑ k, (if S k then c 0 else c b) = 0 := by
    rw [← hsum]
    exact (Finset.sum_congr rfl fun k _ => (hfun k).symm)
  exact sum_ne_zero S (c 0) (c b) hcb ⟨0, hS0⟩ ⟨b, hSb⟩ hsum'

section Reflections

variable {V : Type*} [AddCommGroup V] [Module (ZMod 5) V]

structure ReflData (T : V ≃ₗ[ZMod 5] V) (r : V) (φ : V →ₗ[ZMod 5] ZMod 5) : Prop where
  ne : r ≠ 0
  pair : φ r = 2
  apply : ∀ x, T x = x - φ x • r

theorem ReflData.apply_root {T : V ≃ₗ[ZMod 5] V} {r : V} {φ : V →ₗ[ZMod 5] ZMod 5}
    (h : ReflData T r φ) : T r = -r := by
  rw [h.apply r, h.pair]
  module

theorem ReflData.mul_self {T : V ≃ₗ[ZMod 5] V} {r : V} {φ : V →ₗ[ZMod 5] ZMod 5}
    (h : ReflData T r φ) : T * T = 1 := by
  ext x
  have h1 : T (T x) = T x - φ x • T r := by
    have := congrArg T (h.apply x)
    rw [this, map_sub, map_smul]
  show T (T x) = x
  rw [h1, h.apply_root, h.apply x]
  module

theorem ReflData.conj {T : V ≃ₗ[ZMod 5] V} {r : V} {φ : V →ₗ[ZMod 5] ZMod 5}
    (h : ReflData T r φ) (g : V ≃ₗ[ZMod 5] V) :
    ReflData (g * T * g⁻¹) (g r) (φ ∘ₗ (g.symm : V →ₗ[ZMod 5] V)) where
  ne := fun h0 => h.ne (g.injective (by rw [h0, map_zero]))
  pair := by
    simp [h.pair]
  apply x := by
    have hg : (g⁻¹ : V ≃ₗ[ZMod 5] V) x = g.symm x := rfl
    show g (T (g⁻¹ x)) = x - φ (g.symm x) • g r
    rw [hg, h.apply, map_sub, map_smul, LinearEquiv.apply_symm_apply]

theorem ReflData.mul_apply {T T' : V ≃ₗ[ZMod 5] V} {r r' : V} {φ φ' : V →ₗ[ZMod 5] ZMod 5}
    (h : ReflData T r φ) (h' : ReflData T' r' φ') (x : V) :
    (T * T') x = x - φ' x • r' - φ x • r + (φ r' * φ' x) • r := by
  show T (T' x) = _
  rw [h'.apply x, h.apply, map_sub, map_smul]
  module

@[expose] def step (a b : ZMod 5) (z : ZMod 5 × ZMod 5) : ZMod 5 × ZMod 5 :=
  ((a * b - 1) * z.1 + a * z.2, -b * z.1 - z.2)

theorem exists_inv : ∀ t : ZMod 5, t ≠ 0 → ∃ u : ZMod 5, u * t = 1 := by
  decide

theorem mul_eq_zero_five : ∀ x y : ZMod 5, x * y = 0 → x = 0 ∨ y = 0 := by
  decide

theorem smul_eq_zero_of_ne {W : Type*} [AddCommGroup W] [Module (ZMod 5) W] {c : ZMod 5} {v : W}
    (hv : v ≠ 0) (h : c • v = 0) : c = 0 := by
  by_contra hc
  obtain ⟨u, hu⟩ := exists_inv c hc
  apply hv
  calc v = (u * c) • v := by rw [hu, one_smul]
    _ = u • (c • v) := by rw [mul_smul]
    _ = 0 := by rw [h, smul_zero]

theorem step_two : ∀ a b : ZMod 5, (step a b)^[2] (1, 0) = (1, 0) → (step a b)^[2] (0, 1) = (0, 1) →
    a = 0 ∧ b = 0 := by
  decide

theorem step_three : ∀ a b : ZMod 5, (step a b)^[3] (1, 0) = (1, 0) →
    (step a b)^[3] (0, 1) = (0, 1) → a * b = 1 := by
  decide

theorem refl_pair {T T' : V ≃ₗ[ZMod 5] V} {r r' : V} {φ φ' : V →ₗ[ZMod 5] ZMod 5}
    (h : ReflData T r φ) (h' : ReflData T' r' φ') (hne : T ≠ T') :
    ((T * T') ^ 2 = 1 → φ r' = 0 ∧ φ' r = 0) ∧ ((T * T') ^ 3 = 1 → φ r' * φ' r = 1) := by
  have hU1 : T * T' ≠ 1 := by
    intro h1
    apply hne
    calc T = T * (T * T') := by rw [h1, mul_one]
      _ = T' := by rw [← mul_assoc, h.mul_self, one_mul]
  by_cases hdep : ∃ l : ZMod 5, r' = l • r
  ·
    obtain ⟨l, hl⟩ := hdep
    let ψ : V →ₗ[ZMod 5] ZMod 5 := φ - l • φ'
    have hψr : ψ r = 0 := by
      have h2 : φ' r' = 2 := h'.pair
      rw [hl, map_smul, smul_eq_mul] at h2
      show φ r - l * φ' r = 0
      rw [h.pair]
      linear_combination -h2
    have hU : ∀ x, (T * T') x = x - ψ x • r := by
      intro x
      have hφr' : φ r' = 2 * l := by
        rw [hl, map_smul, smul_eq_mul, h.pair, mul_comm]
      rw [h.mul_apply h' x, hφr', hl]
      show _ = x - (φ x - l * φ' x) • r
      module
    have hpow : ∀ k : ℕ, ∀ x, ((T * T') ^ k) x = x - ((k : ZMod 5) * ψ x) • r := by
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
    have hk : ∀ k : ℕ, (T * T') ^ k = 1 → (k : ZMod 5) ≠ 0 → T * T' = 1 := by
      intro k hk1 hk0
      have hx : ∀ x, ψ x = 0 := by
        intro x
        have h1 : x = x - ((k : ZMod 5) * ψ x) • r := by
          have := hpow k x
          rw [hk1] at this
          exact this
        have h2 : ((k : ZMod 5) * ψ x) • r = 0 := by
          have h3 : x - x = x - (x - ((k : ZMod 5) * ψ x) • r) := by
            rw [← h1]
          simpa using h3.symm
        have h3 := smul_eq_zero_of_ne h.ne h2
        exact (mul_eq_zero_five _ _ h3).resolve_left hk0
      ext x
      rw [hU x, hx x, zero_smul, sub_zero]
      rfl
    exact ⟨fun h2 => absurd (hk 2 h2 (by decide)) hU1, fun h3 => absurd (hk 3 h3 (by decide)) hU1⟩
  ·
    have hind : ∀ s t : ZMod 5, s • r + t • r' = 0 → s = 0 ∧ t = 0 := by
      intro s t hst
      by_cases ht : t = 0
      · subst ht
        rw [zero_smul, add_zero] at hst
        exact ⟨smul_eq_zero_of_ne h.ne hst, rfl⟩
      · exfalso
        apply hdep
        obtain ⟨u, hu⟩ := exists_inv t ht
        refine ⟨-(u * s), ?_⟩
        have h1 : t • r' = -(s • r) := eq_neg_of_add_eq_zero_right hst
        have h2 : r' = u • (-(s • r)) := by
          rw [← h1, smul_smul, hu, one_smul]
        rw [h2]
        module
    set a := φ r' with ha
    set b := φ' r with hb
    have hUr : (T * T') r = (a * b - 1) • r + (-b) • r' := by
      rw [h.mul_apply h' r, h.pair]
      module
    have hUr' : (T * T') r' = a • r + (-1 : ZMod 5) • r' := by
      rw [h.mul_apply h' r', h'.pair]
      module
    have hstep : ∀ x y : ZMod 5, (T * T') (x • r + y • r') =
        (step a b (x, y)).1 • r + (step a b (x, y)).2 • r' := by
      intro x y
      rw [map_add, map_smul, map_smul, hUr, hUr']
      simp only [step]
      module
    have hpow : ∀ k : ℕ, ∀ x y : ZMod 5, ((T * T') ^ k) (x • r + y • r') =
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
    refine ⟨fun h2 => ?_, fun h3 => ?_⟩
    · obtain ⟨c1, c2⟩ := hcoef 2 h2
      exact step_two a b c1 c2
    · obtain ⟨c1, c2⟩ := hcoef 3 h3
      exact step_three a b c1 c2

theorem dichotomy {T T' : V ≃ₗ[ZMod 5] V} {r r' : V} {φ φ' : V →ₗ[ZMod 5] ZMod 5}
    (h : ReflData T r φ) (h' : ReflData T' r' φ') (hne : T ≠ T')
    (hord : (T * T') ^ 1 = 1 ∨ (T * T') ^ 2 = 1 ∨ (T * T') ^ 3 = 1) :
    (φ r' = 0 ∧ φ' r = 0) ∨ φ r' * φ' r = 1 := by
  have hU1 : T * T' ≠ 1 := by
    intro h1
    apply hne
    calc T = T * (T * T') := by rw [h1, mul_one]
      _ = T' := by rw [← mul_assoc, h.mul_self, one_mul]
  obtain ⟨h2, h3⟩ := refl_pair h h' hne
  rcases hord with h1 | h4 | h5
  · exact absurd (by simpa using h1) hU1
  · exact Or.inl (h2 h4)
  · exact Or.inr (h3 h5)

theorem commute_orth {T T' : V ≃ₗ[ZMod 5] V} {r r' : V} {φ φ' : V →ₗ[ZMod 5] ZMod 5}
    (h : ReflData T r φ) (h' : ReflData T' r' φ') (hne : T ≠ T') (hc : T * T' = T' * T) :
    φ r' = 0 ∧ φ' r = 0 := by
  refine (refl_pair h h' hne).1 ?_
  have hcomm : Commute T T' := hc
  rw [hcomm.mul_pow, pow_two T, h.mul_self, pow_two T', h'.mul_self, one_mul]

theorem ReflData.neg {T : V ≃ₗ[ZMod 5] V} {r : V} {φ : V →ₗ[ZMod 5] ZMod 5}
    (h : ReflData T r φ) : ReflData T (-r) (-φ) where
  ne := fun h0 => h.ne (neg_eq_zero.1 h0)
  pair := by
    simp [h.pair]
  apply x := by
    rw [h.apply x]
    simp

theorem ReflData.rescale {T : V ≃ₗ[ZMod 5] V} {r : V} {φ : V →ₗ[ZMod 5] ZMod 5}
    (h : ReflData T r φ) {c μ : ZMod 5} (hcμ : c * μ = 1) :
    ReflData T (μ • r) (c • φ) where
  ne := by
    intro h0
    have h1 := smul_eq_zero_of_ne h.ne h0
    rw [h1, mul_zero] at hcμ
    exact absurd hcμ (by decide)
  pair := by
    rw [LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, h.pair]
    linear_combination 2 * hcμ
  apply x := by
    rw [h.apply x, LinearMap.smul_apply, smul_eq_mul, smul_smul]
    have : c * φ x * μ = φ x := by linear_combination (φ x) * hcμ
    rw [this]

end Reflections

section Star

open Equiv

variable {V : Type*} [AddCommGroup V] [Module (ZMod 5) V]

theorem swap_braid : ∀ j k : Fin 5, j ≠ 4 → k ≠ 4 → j ≠ k → (swap j 4 * swap k 4) ^ 3 = 1 := by
  decide

theorem swap_conj_eq : ∀ j k : Fin 5, j ≠ 4 → k ≠ 4 → j ≠ k →
    swap j k = swap j 4 * swap k 4 * swap j 4 := by
  decide

theorem swap_disjoint_comm : ∀ a b c d : Fin 5,
    (a ≠ b ∧ c ≠ d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) →
    swap a b * swap c d = swap c d * swap a b := by
  decide

theorem swap_ne_of_ne : ∀ a b c d : Fin 5, (a ≠ b ∧ c ≠ d ∧ a ≠ c ∧ a ≠ d) →
    swap a b ≠ swap c d := by
  decide

theorem ReflData.congr {T T' : V ≃ₗ[ZMod 5] V} {r r' : V} {φ φ' : V →ₗ[ZMod 5] ZMod 5}
    (h : ReflData T r φ) (hT : T = T') (hr : r = r') (hφ : φ = φ') : ReflData T' r' φ' := by
  subst hT hr hφ
  exact h

structure StarData (ρ : Perm (Fin 5) →* (V ≃ₗ[ZMod 5] V)) (R : Fin 5 → V)
    (Φ : Fin 5 → V →ₗ[ZMod 5] ZMod 5) : Prop where
  root_four : R 4 = 0
  cov_four : Φ 4 = 0
  base : ∀ k : Fin 5, k ≠ 4 → ReflData (ρ (swap k 4)) (R k) (Φ k)
  cartan : ∀ j k : Fin 5, j ≠ 4 → k ≠ 4 → Φ j (R k) = if j = k then 2 else 1

theorem StarData.refl_all {ρ : Perm (Fin 5) →* (V ≃ₗ[ZMod 5] V)} {R : Fin 5 → V}
    {Φ : Fin 5 → V →ₗ[ZMod 5] ZMod 5} (hS : StarData ρ R Φ) {a b : Fin 5} (hab : a ≠ b) :
    ReflData (ρ (swap a b)) (R b - R a) (Φ b - Φ a) := by
  by_cases ha : a = 4
  · subst ha
    have hb : b ≠ 4 := fun h => hab h.symm
    have := hS.base b hb
    rw [swap_comm]
    simpa [hS.root_four, hS.cov_four] using this
  · by_cases hb : b = 4
    · subst hb
      have := (hS.base a ha).neg
      rw [hS.root_four, hS.cov_four]
      simpa using this
    · have hg := (hS.base b hb).conj (ρ (swap a 4))
      have hA := hS.base a ha
      have c1 : Φ a (R b) = 1 := by
        have := hS.cartan a b ha hb
        simpa [hab] using this
      have c2 : Φ b (R a) = 1 := by
        have := hS.cartan b a hb ha
        simpa [Ne.symm hab] using this
      refine hg.congr ?_ ?_ ?_
      · rw [swap_conj_eq a b ha hb hab, map_mul, map_mul, ← map_inv, swap_inv]
      · rw [hA.apply (R b), c1, one_smul]
      · ext x
        have hgx : (ρ (swap a 4)).symm x = ρ (swap a 4) x := by
          rw [LinearEquiv.symm_apply_eq]
          have := congrArg (fun T : V ≃ₗ[ZMod 5] V => T x) hA.mul_self
          exact this.symm
        show Φ b ((ρ (swap a 4)).symm x) = (Φ b - Φ a) x
        rw [hgx, hA.apply x, map_sub, map_smul, c2]
        simp

structure SwapRep (ρ : Perm (Fin 5) →* (V ≃ₗ[ZMod 5] V)) : Prop where
  inj : Function.Injective ρ
  refl : ∀ a b : Fin 5, a ≠ b →
    ∃ (r : V) (φ : V →ₗ[ZMod 5] ZMod 5), ReflData (ρ (swap a b)) r φ

theorem exists_star {ρ : Perm (Fin 5) →* (V ≃ₗ[ZMod 5] V)} (hρ : SwapRep ρ) :
    ∃ (R : Fin 5 → V) (Φ : Fin 5 → V →ₗ[ZMod 5] ZMod 5), StarData ρ R Φ := by
  choose! r φ hrf using fun (k : Fin 5) (hk : k ≠ 4) => hρ.refl k 4 hk
  have hbraid : ∀ j k : Fin 5, j ≠ 4 → k ≠ 4 → j ≠ k → φ j (r k) * φ k (r j) = 1 := by
    intro j k hj hk hjk
    have hne : ρ (swap j 4) ≠ ρ (swap k 4) := fun h =>
      swap_ne_of_ne j 4 k 4 ⟨hj, hk, hjk, hj⟩ (hρ.inj h)
    refine (refl_pair (hrf j hj) (hrf k hk) hne).2 ?_
    rw [← map_mul, ← map_pow, swap_braid j k hj hk hjk, map_one]
  have hcoc : ∀ j k i : Fin 5, j ≠ 4 → k ≠ 4 → i ≠ 4 → j ≠ k → j ≠ i → k ≠ i →
      φ k (r i) = φ j (r i) * φ k (r j) := by
    intro j k i hj hk hi hjk hji hki
    have hg := (hrf k hk).conj (ρ (swap j 4))
    have hT : ρ (swap j 4) * ρ (swap k 4) * (ρ (swap j 4))⁻¹ = ρ (swap j k) := by
      rw [swap_conj_eq j k hj hk hjk, map_mul, map_mul, ← map_inv, swap_inv]
    have hcomm : ρ (swap j k) * ρ (swap i 4) = ρ (swap i 4) * ρ (swap j k) := by
      rw [← map_mul, ← map_mul, swap_disjoint_comm j k i 4 ⟨hjk, hi, hji, hj, hki, hk⟩]
    have hne : ρ (swap j k) ≠ ρ (swap i 4) := fun h =>
      swap_ne_of_ne j k i 4 ⟨hjk, hi, hji, hj⟩ (hρ.inj h)
    have h1 := (commute_orth (hg.congr hT rfl rfl) (hrf i hi) hne hcomm).1
    have hA := hrf j hj
    have hgx : (ρ (swap j 4)).symm (r i) = ρ (swap j 4) (r i) := by
      rw [LinearEquiv.symm_apply_eq]
      have := congrArg (fun T : V ≃ₗ[ZMod 5] V => T (r i)) hA.mul_self
      exact this.symm
    have h1' : φ k ((ρ (swap j 4)).symm (r i)) = 0 := h1
    rw [hgx, hA.apply (r i), map_sub, map_smul, smul_eq_mul] at h1'
    linear_combination h1'
  let α : Fin 5 → ZMod 5 := fun k => if k = 0 then 1 else φ 0 (r k)
  let β : Fin 5 → ZMod 5 := fun k => if k = 0 then 1 else φ k (r 0)
  have hαβ : ∀ k : Fin 5, k ≠ 4 → α k * β k = 1 := by
    intro k hk
    by_cases hk0 : k = 0
    · simp [α, β, hk0]
    · simp only [α, β, hk0, ite_false]
      exact hbraid 0 k (by decide) hk (Ne.symm hk0)
  refine ⟨fun k => if k = 4 then 0 else β k • r k, fun k => if k = 4 then 0 else α k • φ k, ?_⟩
  refine ⟨by simp, by simp, fun k hk => ?_, fun j k hj hk => ?_⟩
  · have := (hrf k hk).rescale (hαβ k hk)
    simpa [hk] using this
  · simp only [hj, hk, ite_false, LinearMap.smul_apply, map_smul, smul_eq_mul]
    by_cases hjk : j = k
    · subst hjk
      rw [(hrf j hj).pair]
      simp only [ite_true]
      linear_combination 2 * hαβ j hj
    · simp only [hjk, ite_false]
      by_cases hj0 : j = 0
      · subst hj0
        have h0 : k ≠ 0 := fun h => hjk h.symm
        simp only [α, β, h0, ite_true, ite_false]
        linear_combination hbraid k 0 hk (by decide) h0
      · by_cases hk0 : k = 0
        · subst hk0
          simp only [α, β, hj0, ite_true, ite_false]
          linear_combination hbraid 0 j (by decide) hj (Ne.symm hj0)
        · simp only [α, β, hj0, hk0, ite_false]
          rw [hcoc 0 j k (by decide) hj hk (Ne.symm hj0) (Ne.symm hk0) hjk]
          linear_combination (φ 0 (r k) * φ k (r 0)) * hbraid 0 j (by decide) hj (Ne.symm hj0) +
            hbraid 0 k (by decide) hk (Ne.symm hk0)

theorem star_extra {ρ : Perm (Fin 5) →* (V ≃ₗ[ZMod 5] V)} {R : Fin 5 → V}
    {Φ : Fin 5 → V →ₗ[ZMod 5] ZMod 5} (hS : StarData ρ R Φ) (hsum : ∀ x : V, ∑ k : Fin 5, Φ k x = 0)
    {rs : V} {fs : V →ₗ[ZMod 5] ZMod 5}
    (hdich : ∀ a b : Fin 5, a ≠ b →
      (fs (R b - R a) = 0 ∧ (Φ b - Φ a) rs = 0) ∨ fs (R b - R a) * (Φ b - Φ a) rs = 1) :
    ∀ k : Fin 5, k ≠ 4 → Φ k rs = 0 ∧ fs (R k) = 0 := by
  have hcl := clique_five (fun k => Φ k rs) (fun k => fs (R k)) (hsum rs) (by
    intro i j hij
    rcases hdich j i (Ne.symm hij) with ⟨h1, h2⟩ | h
    · left
      rw [map_sub] at h1
      rw [LinearMap.sub_apply] at h2
      exact ⟨sub_eq_zero.1 h2, sub_eq_zero.1 h1⟩
    · right
      rw [map_sub, LinearMap.sub_apply] at h
      linear_combination h)
  intro k hk
  have h1 := (hcl k 4).1
  have h2 := (hcl k 4).2
  simp only [hS.cov_four, hS.root_four, LinearMap.zero_apply, map_zero] at h1 h2
  exact ⟨h1, h2⟩

@[expose] def rootSpace (ρ : Perm (Fin 5) →* (V ≃ₗ[ZMod 5] V)) : Submodule (ZMod 5) V :=
  ⨆ (a : Fin 5) (b : Fin 5) (_ : a ≠ b),
    LinearMap.range ((ρ (swap a b) : V →ₗ[ZMod 5] V) - LinearMap.id)

@[expose] def fixedSpace (ρ : Perm (Fin 5) →* (V ≃ₗ[ZMod 5] V)) : Submodule (ZMod 5) V where
  carrier := {y | ∀ σ, ρ σ y = y}
  add_mem' := by
    intro x y hx hy σ
    rw [map_add, hx σ, hy σ]
  zero_mem' := by
    intro σ
    exact map_zero _
  smul_mem' := by
    intro c x hx σ
    rw [map_smul, hx σ]

theorem star_sum_zero {ρ : Perm (Fin 5) →* (V ≃ₗ[ZMod 5] V)} {R : Fin 5 → V}
    {Φ : Fin 5 → V →ₗ[ZMod 5] ZMod 5} (hS : StarData ρ R Φ)
    (hspan : rootSpace ρ ⊔ fixedSpace ρ = ⊤) : ∀ x : V, ∑ k : Fin 5, Φ k x = 0 := by
  let Ψ : V →ₗ[ZMod 5] ZMod 5 := ∑ k : Fin 5, Φ k
  have hΨ : ∀ x, Ψ x = ∑ k, Φ k x := fun x => by simp [Ψ, LinearMap.sum_apply]
  have hcount : ∀ j : Fin 5, j ≠ 4 →
      ∑ k : Fin 5, (if k = 4 then (0 : ZMod 5) else if k = j then 2 else 1) = 0 := by
    decide
  have hRoot : ∀ j : Fin 5, Ψ (R j) = 0 := by
    intro j
    by_cases hj : j = 4
    · rw [hj, hS.root_four, map_zero]
    · rw [hΨ]
      have : ∀ k : Fin 5, Φ k (R j) = if k = 4 then 0 else if k = j then 2 else 1 := by
        intro k
        by_cases hk : k = 4
        · simp [hk, hS.cov_four]
        · rw [hS.cartan k j hk hj]
          simp [hk]
      simp only [this]
      exact hcount j hj
  have hRt : rootSpace ρ ≤ LinearMap.ker Ψ := by
    refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
    rintro _ ⟨y, rfl⟩
    have h := hS.refl_all hab
    rw [LinearMap.mem_ker]
    have e : ((ρ (swap a b) : V →ₗ[ZMod 5] V) - LinearMap.id : V →ₗ[ZMod 5] V) y =
        -((Φ b - Φ a) y) • (R b - R a) := by
      show ρ (swap a b) y - y = _
      rw [h.apply y]
      module
    rw [e, map_smul, map_sub, hRoot b, hRoot a]
    simp
  have hFx : fixedSpace ρ ≤ LinearMap.ker Ψ := by
    intro y hy
    rw [LinearMap.mem_ker, hΨ]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = 4
    · rw [hk, hS.cov_four]
      rfl
    · have h := hS.base k hk
      have hy' : ρ (swap k 4) y = y := hy _
      rw [h.apply y] at hy'
      have h2 : Φ k y • R k = 0 := by
        have h3 : y - Φ k y • R k - y = 0 := sub_eq_zero.2 hy'
        rw [sub_sub_cancel_left] at h3
        exact neg_eq_zero.1 h3
      exact smul_eq_zero_of_ne h.ne h2
  intro x
  have hx : x ∈ rootSpace ρ ⊔ fixedSpace ρ := by
    rw [hspan]
    trivial
  rw [← hΨ]
  exact sup_le hRt hFx hx

theorem part_one_core {ρ : Perm (Fin 5) →* (V ≃ₗ[ZMod 5] V)} (hρ : SwapRep ρ) [Finite V]
    (hspan : rootSpace ρ ⊔ fixedSpace ρ = ⊤) {s : V ≃ₗ[ZMod 5] V} {rs : V}
    {fs : V →ₗ[ZMod 5] ZMod 5} (hs : ReflData s rs fs)
    (hne : ∀ a b : Fin 5, a ≠ b → s ≠ ρ (swap a b))
    (hord : ∀ a b : Fin 5, a ≠ b → orderOf (s * ρ (swap a b)) ≤ 3) :
    (∀ a b : Fin 5, a ≠ b → s * ρ (swap a b) = ρ (swap a b) * s) ∧
    (∀ a b : Fin 5, a ≠ b → ∀ x : V, fs (ρ (swap a b) x - x) = 0) ∧
    ∀ σ : Perm (Fin 5), ρ σ rs = rs := by
  obtain ⟨R, Φ, hS⟩ := exists_star hρ
  have hsum := star_sum_zero hS hspan
  have hFin : Finite (V ≃ₗ[ZMod 5] V) :=
    Finite.of_injective (fun f : V ≃ₗ[ZMod 5] V => (f : V → V))
      (fun f g h => LinearEquiv.ext (congrFun h))
  have hdich : ∀ a b : Fin 5, a ≠ b →
      (fs (R b - R a) = 0 ∧ (Φ b - Φ a) rs = 0) ∨ fs (R b - R a) * (Φ b - Φ a) rs = 1 := by
    intro a b hab
    refine dichotomy hs (hS.refl_all hab) (hne a b hab) ?_
    have hpos := orderOf_pos (s * ρ (swap a b))
    have hle := hord a b hab
    have hpow := pow_orderOf_eq_one (s * ρ (swap a b))
    have hcases : orderOf (s * ρ (swap a b)) = 1 ∨ orderOf (s * ρ (swap a b)) = 2 ∨
        orderOf (s * ρ (swap a b)) = 3 := by omega
    rcases hcases with h | h | h <;> rw [h] at hpow
    · exact Or.inl hpow
    · exact Or.inr (Or.inl hpow)
    · exact Or.inr (Or.inr hpow)
  have hex := star_extra hS hsum hdich
  have hz : ∀ k : Fin 5, Φ k rs = 0 ∧ fs (R k) = 0 := by
    intro k
    by_cases hk : k = 4
    · subst hk
      simp [hS.cov_four, hS.root_four]
    · exact hex k hk
  have hz1 : ∀ a b : Fin 5, fs (R b - R a) = 0 := by
    intro a b
    rw [map_sub, (hz a).2, (hz b).2, sub_zero]
  have hz2 : ∀ a b : Fin 5, (Φ b - Φ a) rs = 0 := by
    intro a b
    rw [LinearMap.sub_apply, (hz a).1, (hz b).1, sub_zero]
  refine ⟨fun a b hab => ?_, fun a b hab x => ?_, fun σ => ?_⟩
  · have hτ := hS.refl_all hab
    ext x
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    have e1 := hs.mul_apply hτ x
    have e2 := hτ.mul_apply hs x
    rw [LinearEquiv.mul_apply] at e1 e2
    rw [e1, e2, hz1 a b, hz2 a b]
    module
  · have hτ := hS.refl_all hab
    rw [hτ.apply x, sub_sub_cancel_left, map_neg, map_smul, hz1 a b]
    simp
  · induction σ using Equiv.Perm.swap_induction_on with
    | one =>
      rw [map_one]
      rfl
    | swap_mul f x y hxy ih =>
      have hτ := hS.refl_all hxy
      rw [map_mul, LinearEquiv.mul_apply, ih, hτ.apply rs, hz2 x y]
      simp

end Star

end Sec138I

end CFSG.RankThree.PartOne
