module

public import CFSG.Sporadic.Co1Patterson.TitsMulti
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Sporadic.Co1Patterson

open SimpleGraph

variable {V : Type*} {X : Type*} [Group X] [MulAction X V]

@[expose] def triOrb {ι : Type*} (v w : V) (u : ι → V) : Set V → Prop :=
  fun S => ∃ (g : X) (j : ι), S = (g • ·) '' {v, w, u j}

theorem image_smul_triple (g : X) (a b c : V) :
    (g • ·) '' ({a, b, c} : Set V) = {g • a, g • b, g • c} := by
  simp [Set.image_insert_eq, Set.image_singleton]

theorem triOrb_image_smul {ι : Type*} {v w : V} {u : ι → V} (g : X) {S : Set V}
    (h : triOrb (X := X) v w u S) : triOrb (X := X) v w u ((g • ·) '' S) := by
  obtain ⟨g', j, rfl⟩ := h
  refine ⟨g * g', j, ?_⟩
  rw [Set.image_image]
  simp only [mul_smul]

theorem mem_triple {a b c x : V} : x ∈ ({a, b, c} : Set V) ↔ x = a ∨ x = b ∨ x = c := by
  simp

theorem exists_smul_of_triOrb {ι : Type*} {v w : V} {u : ι → V} {j : ι} {τ ρ : X}
    (hτv : τ • v = w) (hτw : τ • w = v) (hτu : τ • u j = u j) (hρv : ρ • v = w)
    (hρw : ρ • w = u j) (hρu : ρ • u j = v) {g : X} {y₁ y₂ : V} (hv1 : v ≠ y₁) (hv2 : v ≠ y₂)
    (h12 : y₁ ≠ y₂) (hS : ({v, y₁, y₂} : Set V) = (g • ·) '' {v, w, u j}) :
    ∃ g' : X, g' • v = v ∧ g' • w = y₁ ∧ g' • u j = y₂ := by
  rw [image_smul_triple] at hS
  have hmem : ∀ x, x ∈ ({v, y₁, y₂} : Set V) ↔ x ∈ ({g • v, g • w, g • u j} : Set V) := fun x =>
    by rw [hS]
  simp only [mem_triple] at hmem
  rcases (hmem v).1 (Or.inl rfl) with hv | hv | hv <;>
  rcases (hmem y₁).1 (Or.inr (Or.inl rfl)) with h1 | h1 | h1 <;>
  rcases (hmem y₂).1 (Or.inr (Or.inr rfl)) with h2 | h2 | h2 <;>
  first
  | exact absurd (hv.trans h1.symm) hv1
  | exact absurd (hv.trans h2.symm) hv2
  | exact absurd (h1.trans h2.symm) h12
  | exact ⟨g, hv.symm, h1.symm, h2.symm⟩
  | exact ⟨g * (τ * ρ), by simp only [mul_smul, hρv, hτw]; exact hv.symm,
      by simp only [mul_smul, hρw, hτu]; exact h1.symm,
      by simp only [mul_smul, hρu, hτv]; exact h2.symm⟩
  | exact ⟨g * τ, by simp only [mul_smul, hτv]; exact hv.symm,
      by simp only [mul_smul, hτw]; exact h1.symm, by simp only [mul_smul, hτu]; exact h2.symm⟩
  | exact ⟨g * ρ, by simp only [mul_smul, hρv]; exact hv.symm,
      by simp only [mul_smul, hρw]; exact h1.symm, by simp only [mul_smul, hρu]; exact h2.symm⟩
  | exact ⟨g * (ρ * ρ), by simp only [mul_smul, hρv, hρw]; exact hv.symm,
      by simp only [mul_smul, hρw, hρu]; exact h1.symm,
      by simp only [mul_smul, hρu, hρv]; exact h2.symm⟩
  | exact ⟨g * (ρ * τ), by simp only [mul_smul, hτv, hρw]; exact hv.symm,
      by simp only [mul_smul, hτw, hρv]; exact h1.symm,
      by simp only [mul_smul, hτu, hρu]; exact h2.symm⟩

theorem smul_mem_of_image_eq {g : X} {a b c : V}
    (h : (g • ·) '' ({a, b, c} : Set V) = {a, b, c}) (x : V) (hx : x ∈ ({a, b, c} : Set V)) :
    g • x ∈ ({a, b, c} : Set V) := by
  rw [← h]
  exact ⟨x, hx, rfl⟩

@[expose] def TitsDataBy.ofOrbits {Γ : SimpleGraph V} {ι : Type*} (v w : V) (u : ι → V)
    (Xv Xe : Subgroup X) (Xt : ι → Subgroup X)
    (hadj : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    (hconn : Γ.Preconnected) (hΓ : TriangulableBy Γ (triOrb (X := X) v w u))
    (hvw : Γ.Adj v w) (hloc : ∀ y, Γ.Adj v y → ∃ g : X, g • v = v ∧ g • w = y)
    (hswap : ∃ g : X, g • v = w ∧ g • w = v) (hXv : ∀ g, g ∈ Xv ↔ g • v = v)
    (hXe : ∀ g, g ∈ Xe ↔ (g • v = v ∧ g • w = w) ∨ (g • v = w ∧ g • w = v))
    (hstab : ∀ j, ∀ g ∈ Xt j, (g • ·) '' ({v, w, u j} : Set V) = {v, w, u j})
    (hτ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = v)
    (hρ : ∀ j, ∃ g ∈ Xt j, g • v = w ∧ g • w = u j ∧ g • u j = v) :
    TitsDataBy Γ (triOrb (X := X) v w u) X ι where
  v := v
  w := w
  u := u
  Xv := Xv
  Xe := Xe
  Xt := Xt
  hadj := hadj
  hTinv g _ hS := triOrb_image_smul g hS
  hconn := hconn
  hΓ := hΓ
  hvw := hvw
  hloc := hloc
  hswap := hswap
  hXv := hXv
  hXe := hXe
  hXt j g hg := by
    have := smul_mem_of_image_eq (hstab j g hg) v (by simp)
    simpa only [mem_triple] using this
  hτ := hτ
  hρ := hρ
  htri y₁ y₂ h₁ h₂ h₃ hT := by
    obtain ⟨g, j, hS⟩ := hT
    obtain ⟨τ, hτm, hτv, hτw⟩ := hτ j
    obtain ⟨ρ, -, hρv, hρw, hρu⟩ := hρ j
    have huv : u j ≠ v := fun e => hvw.ne (by
      have : ρ • v = ρ • u j := by rw [e]
      rw [hρv, hρu] at this
      exact this.symm)
    have huw : u j ≠ w := fun e => hvw.ne (by
      have : ρ • v = ρ • w := by rw [hρv, hρw, e]
      exact smul_left_cancel ρ this)
    have hτu : τ • u j = u j := by
      have hm := smul_mem_of_image_eq (hstab j τ hτm) (u j) (by simp)
      simp only [mem_triple] at hm
      rcases hm with hm | hm | hm
      · exact absurd (smul_left_cancel τ (hm.trans hτw.symm)) huw
      · exact absurd (smul_left_cancel τ (hm.trans hτv.symm)) huv
      · exact hm
    obtain ⟨g', h1, h2, h3⟩ := exists_smul_of_triOrb hτv hτw hτu hρv hρw hρu h₁.ne h₃.ne.symm
      h₂.ne hS
    exact ⟨j, g', h1, h2, h3⟩

end CFSG.Sporadic.Co1Patterson
