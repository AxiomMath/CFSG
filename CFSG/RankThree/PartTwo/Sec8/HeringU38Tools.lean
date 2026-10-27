module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace HeringU38

variable {G : Type*} [Group G]

open scoped commutatorElement

theorem commutator_conj_mem (C : Subgroup G) (b : G) {c : G} (hc : c ∈ C)
    {x : G} (hx : x ∈ ⁅C, Subgroup.zpowers b⁆) : c * x * c⁻¹ ∈ ⁅C, Subgroup.zpowers b⁆ := by
  rw [Subgroup.commutator_def] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨p, hp, q, hq, rfl⟩ := hy
    have h1 : c * ⁅p, q⁆ * c⁻¹ = ⁅c * p, q⁆ * ⁅c, q⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨c * p, Subgroup.mul_mem _ hc hp, q, hq, rfl⟩)
      (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨c, hc, q, hq, rfl⟩))
  | one => simpa using Subgroup.one_mem _
  | mul y z _ _ hy hz =>
    have : c * (y * z) * c⁻¹ = (c * y * c⁻¹) * (c * z * c⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hy hz
  | inv y _ hy =>
    have : c * y⁻¹ * c⁻¹ = (c * y * c⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hy

theorem pow_mul_mem (N : Subgroup G) {θ n : G} (hθ : θ ∈ Subgroup.normalizer (N : Set G))
    (hn : n ∈ N) (m : ℕ) : ∃ n' ∈ N, (n * θ) ^ m = n' * θ ^ m := by
  induction m with
  | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
  | succ m ih =>
    obtain ⟨n', hn', h⟩ := ih
    have hθm : θ ^ m ∈ Subgroup.normalizer (N : Set G) := Subgroup.pow_mem _ hθ m
    have hconj : θ ^ m * n * (θ ^ m)⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hθm n).mp hn
    refine ⟨n' * (θ ^ m * n * (θ ^ m)⁻¹), Subgroup.mul_mem _ hn' hconj, ?_⟩
    rw [pow_succ, h]
    group

theorem mem_of_mul_coprime {N : Subgroup G} {θ n t : G}
    (hθ : θ ∈ Subgroup.normalizer (N : Set G)) (hn : n ∈ N)
    (hcop : Nat.Coprime (orderOf θ) (orderOf t)) (ht : t = n * θ) : t ∈ N := by
  obtain ⟨n', hn', h⟩ := pow_mul_mem N hθ hn (orderOf θ)
  rw [pow_orderOf_eq_one, mul_one, ← ht] at h
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm, h]
  exact Subgroup.pow_mem _ hn' m

theorem mem_of_mul_odd {N : Subgroup G} {θ n t : G} (hθ : θ ∈ Subgroup.normalizer (N : Set G))
    (hn : n ∈ N) (hodd : Odd (orderOf θ)) (ht : t = n * θ) (ht2 : ∃ k : ℕ, t ^ 2 ^ k = 1) :
    t ∈ N := by
  obtain ⟨k, hk⟩ := ht2
  have h2 : orderOf t ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  exact mem_of_mul_coprime hθ hn
    (Nat.Coprime.coprime_dvd_right h2 (Nat.Coprime.pow_right _ hodd.coprime_two_right)) ht

theorem le_normalizer_of_conj_mem {A H : Subgroup G} (h : ∀ g ∈ A, ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    A ≤ Subgroup.normalizer (H : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h g hg x hx, fun hx => ?_⟩
  have := h g⁻¹ (Subgroup.inv_mem _ hg) _ hx
  simpa [mul_assoc] using this

theorem mem_normalizer_of_conj_cube {H : Subgroup G} {g : G} (hg3 : g ^ 3 = 1)
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h x hx, fun hx => ?_⟩
  have h3 : g * g * g = 1 := by rw [← pow_three']; exact hg3
  have e : g * (g * (g * x * g⁻¹) * g⁻¹) * g⁻¹ = x := by
    calc g * (g * (g * x * g⁻¹) * g⁻¹) * g⁻¹ = (g * g * g) * x * (g * g * g)⁻¹ := by group
      _ = x := by rw [h3]; simp
  have := h _ (h _ hx)
  rwa [e] at this

end HeringU38
