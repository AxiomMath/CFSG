module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.Sporadic.Co2Smith

open Function

section Stable

variable {M : Type*} [Group M] {n : ℕ} (e : Fin n → M)

@[expose] def ConjStable (g : M) : Prop := ∀ k, ∃ k', g * e k * g⁻¹ = e k'

@[expose] noncomputable def cnt (x : M) : ℕ := Nat.card {k : Fin n // e k * x ∈ Set.range e}

@[expose] def adj (a b : Fin n) : Prop := a ≠ b ∧ cnt e (e a * e b) = 2

variable {e}

@[expose] noncomputable def cfun {g : M} (hg : ConjStable e g) (k : Fin n) : Fin n :=
  Classical.choose (hg k)

theorem cfun_spec {g : M} (hg : ConjStable e g) (k : Fin n) : e (cfun hg k) = g * e k * g⁻¹ :=
  (Classical.choose_spec (hg k)).symm

theorem cfun_injective (he : Injective e) {g : M} (hg : ConjStable e g) : Injective (cfun hg) := by
  intro a b h
  apply he
  have e1 := congrArg e h
  rw [cfun_spec hg a, cfun_spec hg b] at e1
  simpa using e1

@[expose] noncomputable def cperm (he : Injective e) {g : M} (hg : ConjStable e g) :
    Equiv.Perm (Fin n) :=
  Equiv.ofBijective (cfun hg) (Finite.injective_iff_bijective.1 (cfun_injective he hg))

theorem cperm_spec (he : Injective e) {g : M} (hg : ConjStable e g) (k : Fin n) :
    e (cperm he hg k) = g * e k * g⁻¹ :=
  cfun_spec hg k

@[expose] noncomputable def chom (he : Injective e) (S : Subgroup M)
    (hS : ∀ g ∈ S, ConjStable e g) : S →* Equiv.Perm (Fin n) where
  toFun g := cperm he (hS g g.2)
  map_one' := Equiv.ext fun k => he (by
    rw [cperm_spec he _ k, Subgroup.coe_one, one_mul, inv_one, mul_one, Equiv.Perm.one_apply])
  map_mul' g h := Equiv.ext fun k => he (by
    rw [cperm_spec he _ k, Equiv.Perm.mul_apply, cperm_spec he _ _, cperm_spec he _ k,
      Subgroup.coe_mul]
    group)

theorem chom_spec (he : Injective e) (S : Subgroup M) (hS : ∀ g ∈ S, ConjStable e g) (g : S)
    (k : Fin n) :
    e (chom he S hS g k) = g * e k * (g : M)⁻¹ :=
  cperm_spec he (hS g g.2) k

theorem chom_eq_of_spec (he : Injective e) (S : Subgroup M) (hS : ∀ g ∈ S, ConjStable e g) (g : S)
    (σ : Equiv.Perm (Fin n)) (h : ∀ k, e (σ k) = g * e k * (g : M)⁻¹) : chom he S hS g = σ :=
  Equiv.ext fun k => he (by rw [chom_spec he S hS, h])

theorem chom_eq_one_iff (he : Injective e) (S : Subgroup M) (hS : ∀ g ∈ S, ConjStable e g) (g : S) :
    chom he S hS g = 1 ↔ ∀ k, g * e k = e k * g := by
  constructor
  · intro h k
    have e1 := chom_spec he S hS g k
    rw [h, Equiv.Perm.one_apply] at e1
    rw [eq_mul_inv_iff_mul_eq] at e1
    exact e1.symm
  · intro h
    refine chom_eq_of_spec he S hS g 1 fun k => ?_
    rw [Equiv.Perm.one_apply, h k, mul_inv_cancel_right]

theorem cnt_conj (he : Injective e) (S : Subgroup M) (hS : ∀ g ∈ S, ConjStable e g) (g : S)
    (x : M) :
    cnt e ((g : M) * x * (g : M)⁻¹) = cnt e x := by
  have hmem : ∀ y : M, (g : M) * y * (g : M)⁻¹ ∈ Set.range e ↔ y ∈ Set.range e := by
    intro y
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨chom he S hS g⁻¹ j, ?_⟩
      rw [chom_spec he S hS, hj, Subgroup.coe_inv, inv_inv]
      group
    · rintro ⟨j, rfl⟩
      exact ⟨chom he S hS g j, chom_spec he S hS g j⟩
  have h : ∀ k, e k * x ∈ Set.range e ↔
      e (chom he S hS g k) * ((g : M) * x * (g : M)⁻¹) ∈ Set.range e := by
    intro k
    rw [chom_spec he S hS, show (g : M) * e k * (g : M)⁻¹ * ((g : M) * x * (g : M)⁻¹) =
      (g : M) * (e k * x) * (g : M)⁻¹ by group, hmem]
  exact (Nat.card_congr (Equiv.subtypeEquiv (chom he S hS g) h)).symm

theorem adj_chom (he : Injective e) (S : Subgroup M) (hS : ∀ g ∈ S, ConjStable e g) (g : S)
    (a b : Fin n) :
    adj e (chom he S hS g a) (chom he S hS g b) ↔ adj e a b := by
  unfold adj
  rw [chom_spec he S hS, chom_spec he S hS,
    show (g : M) * e a * (g : M)⁻¹ * ((g : M) * e b * (g : M)⁻¹) =
      (g : M) * (e a * e b) * (g : M)⁻¹ by group,
    cnt_conj he S hS g, (chom he S hS g).injective.ne_iff]

end Stable


theorem cnt_map {M M' : Type*} [Group M] [Group M'] {n : ℕ} (f : M →* M') (hf : Injective f)
    (e : Fin n → M) (x : M) : cnt (f ∘ e) (f x) = cnt e x := by
  unfold cnt
  refine Nat.card_congr (Equiv.subtypeEquivRight fun k => ?_)
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, hf ?_⟩
    rw [map_mul]
    exact hj
  · rintro ⟨j, hj⟩
    exact ⟨j, by simp only [Function.comp_apply, ← map_mul, hj]⟩

theorem adj_map {M M' : Type*} [Group M] [Group M'] {n : ℕ} (f : M →* M') (hf : Injective f)
    (e : Fin n → M) (a b : Fin n) : adj (f ∘ e) a b ↔ adj e a b := by
  unfold adj
  rw [show (f ∘ e) a * (f ∘ e) b = f (e a * e b) by simp, cnt_map f hf]

theorem eq_of_transitive_of_le {n : ℕ} {A X : Subgroup (Equiv.Perm (Fin n))} (b : Fin n)
    (hXA : X ≤ A) (htrans : ∀ k, ∃ σ ∈ X, σ b = k)
    (hstab : ∀ σ ∈ A, σ b = b → σ ∈ X) : X = A := by
  refine le_antisymm hXA fun σ hσ => ?_
  obtain ⟨τ, hτ, hτb⟩ := htrans (σ b)
  have h1 : τ⁻¹ * σ ∈ X := hstab _ (A.mul_mem (A.inv_mem (hXA hτ)) hσ) (by
    rw [Equiv.Perm.mul_apply, ← hτb]
    exact τ.symm_apply_apply b)
  have h2 := X.mul_mem hτ h1
  rwa [mul_inv_cancel_left] at h2

end CFSG.Sporadic.Co2Smith
