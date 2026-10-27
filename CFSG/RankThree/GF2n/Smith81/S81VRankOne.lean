module

public import CFSG.RankThree.GF2n.Smith81.S81VTwist
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open Module

structure RankOneData (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V] where
  N : Type
  [acg : AddCommGroup N]
  [mod : Module K N]
  [fin : Module.Finite K N]
  ρ : N → (V ≃ₗ[K] V)
  ρ_add : ∀ n m : N, ρ (n + m) = ρ n * ρ m
  τ : N →ₗ[K] K
  n₁ : N
  τ_n₁ : τ n₁ = 1
  Pg : Type
  [grp : Group Pg]
  a : Pg →* (V ≃ₗ[K] V)
  Ad : Pg →* (N ≃ₗ[K] N)
  Ad_spec : ∀ (g : Pg) (n : N), ρ (Ad g n) = a g * ρ n * (a g)⁻¹
  d : Kˣ →* Pg
  Ad_d : ∀ c : Kˣ, Ad (d c) n₁ = (c : K) ^ 2 • n₁
  s : V ≃ₗ[K] V
  s_sq : s * s = 1
  s_d : ∀ c : Kˣ, s * a (d c) * s = (a (d c))⁻¹
  ker_stab : ∀ n : N, τ n = 0 → ∃ g : Pg, a g = s * ρ n * s
  lemmaS : ∀ n : N, n ≠ 0 → ∃ g : Pg, τ (Ad g n) ≠ 0

attribute [instance] RankOneData.acg RankOneData.mod RankOneData.fin RankOneData.grp

private theorem one_apply_aux {R M : Type} [Semiring R] [AddCommMonoid M] [Module R M] (x : M) :
    (1 : M ≃ₗ[R] M) x = x := rfl

namespace RankOneData

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] (D : RankOneData K V)

@[expose] def X (t : K) : V ≃ₗ[K] V := D.ρ (t • D.n₁)

theorem X_def (t : K) : D.X t = D.ρ (t • D.n₁) := rfl

@[expose] def fix : Submodule K V where
  carrier := {v | ∀ n, D.ρ n v = v}
  add_mem' {v w} hv hw n := by rw [map_add, hv n, hw n]
  zero_mem' n := map_zero _
  smul_mem' c v hv n := by rw [map_smul, hv n]

theorem mem_fix {v : V} : v ∈ D.fix ↔ ∀ n, D.ρ n v = v := Iff.rfl

@[expose] def V1 (β : V →ₗ[K] V →ₗ[K] K) : Submodule K V where
  carrier := {w | (∀ v ∈ D.fix, β v w = 0) ∧ ∀ n, D.ρ n w - w ∈ D.fix}
  add_mem' {w w'} hw hw' := by
    refine ⟨fun v hv => ?_, fun n => ?_⟩
    · rw [map_add, hw.1 v hv, hw'.1 v hv, add_zero]
    · have : D.ρ n (w + w') - (w + w') = (D.ρ n w - w) + (D.ρ n w' - w') := by
        rw [map_add]; abel
      rw [this]
      exact D.fix.add_mem (hw.2 n) (hw'.2 n)
  zero_mem' := ⟨fun v _ => by simp, fun n => by simp⟩
  smul_mem' c w hw := by
    refine ⟨fun v hv => ?_, fun n => ?_⟩
    · rw [map_smul, hw.1 v hv, smul_zero]
    · have : D.ρ n (c • w) - c • w = c • (D.ρ n w - w) := by rw [map_smul, smul_sub]
      rw [this]
      exact D.fix.smul_mem c (hw.2 n)

theorem mem_V1 {β : V →ₗ[K] V →ₗ[K] K} {w : V} :
    w ∈ D.V1 β ↔ (∀ v ∈ D.fix, β v w = 0) ∧ ∀ n, D.ρ n w - w ∈ D.fix := Iff.rfl

variable [CharP K 2]

theorem ρ_zero : D.ρ 0 = 1 := by
  have h := D.ρ_add 0 0
  rw [add_zero] at h
  have h2 : D.ρ 0 * 1 = D.ρ 0 * D.ρ 0 := by rw [mul_one]; exact h
  exact (mul_left_cancel h2).symm

theorem ρ_mul_self (n : D.N) : D.ρ n * D.ρ n = 1 := by
  have h2 : n + n = 0 := by
    rw [← two_smul K n, CharTwo.two_eq_zero, zero_smul]
  rw [← D.ρ_add, h2, D.ρ_zero]

theorem ρ_comm (n m : D.N) : D.ρ n * D.ρ m = D.ρ m * D.ρ n := by
  rw [← D.ρ_add, ← D.ρ_add, add_comm]

theorem X_zero : D.X 0 = 1 := by
  simp [X, D.ρ_zero]

theorem X_add (s t : K) : D.X (s + t) = D.X s * D.X t := by
  simp only [X, add_smul, D.ρ_add]

theorem X_mul_self (t : K) : D.X t * D.X t = 1 := D.ρ_mul_self _

theorem ρ_eq_ker_mul_X (n : D.N) :
    ∃ n' : D.N, D.τ n' = 0 ∧ D.ρ n = D.ρ n' * D.X (D.τ n) := by
  refine ⟨n - D.τ n • D.n₁, ?_, ?_⟩
  · rw [map_sub, map_smul, D.τ_n₁, smul_eq_mul, mul_one, sub_self]
  · show D.ρ n = D.ρ (n - D.τ n • D.n₁) * D.ρ (D.τ n • D.n₁)
    rw [← D.ρ_add, sub_add_cancel]

theorem a_mem_fix (g : D.Pg) {v : V} (hv : v ∈ D.fix) : D.a g v ∈ D.fix := by
  rw [mem_fix] at hv ⊢
  intro n
  have h1 : D.Ad g ((D.Ad g).symm n) = n := (D.Ad g).apply_symm_apply n
  have h2 := D.Ad_spec g ((D.Ad g).symm n)
  rw [h1] at h2
  have h3 : ∀ x : V, (D.a g)⁻¹ (D.a g x) = x := fun x => by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel, one_apply_aux]
  rw [h2, LinearEquiv.mul_apply, LinearEquiv.mul_apply, h3, hv]

theorem exists_scalar [FiniteDimensional K V] (hfix : finrank K D.fix = 1) {v₀ : V}
    (hv₀ : v₀ ∈ D.fix) (hv0 : v₀ ≠ 0) (g : D.Pg) : ∃ c : K, D.a g v₀ = c • v₀ := by
  have hmem : D.a g v₀ ∈ D.fix := D.a_mem_fix g hv₀
  have hne : (⟨v₀, hv₀⟩ : D.fix) ≠ 0 := by
    intro h
    exact hv0 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hfix hne ⟨D.a g v₀, hmem⟩
  exact ⟨c, by simpa using (congrArg Subtype.val hc).symm⟩

theorem exists_char [Fintype K] [FiniteDimensional K V] (hfix : finrank K D.fix = 1) {v₀ : V}
    (hv₀ : v₀ ∈ D.fix) (hv0 : v₀ ≠ 0) :
    ∃ k : ℕ, ∀ c : Kˣ, D.a (D.d c) v₀ = (c : K) ^ k • v₀ := by
  choose χ hχ using fun c : Kˣ => D.exists_scalar hfix hv₀ hv0 (D.d c)
  have hone : χ 1 = 1 := by
    apply smul_left_injective K hv0
    show χ 1 • v₀ = (1 : K) • v₀
    rw [← hχ 1, map_one, map_one, one_apply_aux, one_smul]
  have hmul : ∀ c c' : Kˣ, χ (c * c') = χ c * χ c' := by
    intro c c'
    have key : D.a (D.d (c * c')) v₀ = (χ c * χ c') • v₀ := by
      rw [map_mul, map_mul, LinearEquiv.mul_apply, hχ c', map_smul, hχ c, smul_smul,
        mul_comm (χ c') (χ c)]
    apply smul_left_injective K hv0
    show χ (c * c') • v₀ = (χ c * χ c') • v₀
    rw [← hχ (c * c'), key]
  have hne : ∀ c : Kˣ, χ c ≠ 0 := by
    intro c h0
    have h1 := hmul c c⁻¹
    rw [mul_inv_cancel, hone, h0, zero_mul] at h1
    exact one_ne_zero h1
  have hpow : ∀ (g : Kˣ) (m : ℕ), χ (g ^ m) = χ g ^ m := by
    intro g m
    induction m with
    | zero => simp [hone]
    | succ m ih => rw [pow_succ g m, hmul, ih, pow_succ (χ g) m]
  obtain ⟨g, hg⟩ : ∃ g : Kˣ, ∀ y : Kˣ, y ∈ Submonoid.powers g := IsCyclic.exists_monoid_generator
  obtain ⟨k, hk⟩ := hg (Units.mk0 (χ g) (hne g))
  have hkK : (g : K) ^ k = χ g := by
    have := congrArg Units.val hk
    simpa using this
  refine ⟨k, fun c => ?_⟩
  obtain ⟨m, hm⟩ := hg c
  have hχc : χ c = (c : K) ^ k := by
    rw [← hm, hpow, ← hkK, Units.val_pow_eq_pow_val, pow_right_comm]
  rw [hχ c, hχc]

theorem torus_conj_X (c : Kˣ) (t : K) :
    D.a (D.d c) * D.X t * (D.a (D.d c))⁻¹ = D.X ((c : K) ^ 2 * t) := by
  have h1 : D.Ad (D.d c) (t • D.n₁) = ((c : K) ^ 2 * t) • D.n₁ := by
    rw [map_smul, D.Ad_d, smul_smul, mul_comm]
  simp only [X]
  rw [← h1, D.Ad_spec]

theorem ker_fixes_sv [FiniteDimensional K V] (hfix : finrank K D.fix = 1) {v₀ : V}
    (hv₀ : v₀ ∈ D.fix) (hv0 : v₀ ≠ 0) {n : D.N} (hn : D.τ n = 0) :
    D.ρ n (D.s v₀) = D.s v₀ := by
  obtain ⟨g, hg⟩ := D.ker_stab n hn
  obtain ⟨c, hc⟩ := D.exists_scalar hfix hv₀ hv0 g
  have hρ : D.ρ n = D.s * D.a g * D.s := by
    calc D.ρ n = (D.s * D.s) * D.ρ n * (D.s * D.s) := by rw [D.s_sq, one_mul, mul_one]
      _ = D.s * (D.s * D.ρ n * D.s) * D.s := by simp only [mul_assoc]
      _ = D.s * D.a g * D.s := by rw [hg]
  have hsq : D.a g * D.a g = 1 := by
    rw [hg]
    calc D.s * D.ρ n * D.s * (D.s * D.ρ n * D.s)
        = D.s * D.ρ n * (D.s * D.s) * D.ρ n * D.s := by simp only [mul_assoc]
      _ = D.s * (D.ρ n * D.ρ n) * D.s := by rw [D.s_sq, mul_one]; simp only [mul_assoc]
      _ = 1 := by rw [D.ρ_mul_self, mul_one, D.s_sq]
  have hss : ∀ x : V, D.s (D.s x) = x := fun x => by
    rw [← LinearEquiv.mul_apply, D.s_sq, one_apply_aux]
  have h1 : D.a g (D.a g v₀) = v₀ := by
    rw [← LinearEquiv.mul_apply, hsq, one_apply_aux]
  have hcc : c * c = 1 := by
    apply smul_left_injective K hv0
    show (c * c) • v₀ = (1 : K) • v₀
    rw [one_smul]
    calc (c * c) • v₀ = c • (c • v₀) := (smul_smul c c v₀).symm
      _ = c • D.a g v₀ := by rw [hc]
      _ = D.a g (c • v₀) := (map_smul (D.a g) c v₀).symm
      _ = D.a g (D.a g v₀) := by rw [hc]
      _ = v₀ := h1
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : (c - 1) * (c - 1) = 0 := by linear_combination hcc + (1 - c) * h2
  have hc1 : c = 1 := sub_eq_zero.mp (mul_self_eq_zero.mp h3)
  rw [hρ, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hss, hc, map_smul, hc1, one_smul]

end RankOneData

end CFSG.RankThree.GF2n.Smith81.S81V
