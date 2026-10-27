module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoBase

public section

namespace CFSG.Quasithin.TitsGeo

open CFSG.Quasithin CFSG.Open

universe u v

variable {X : Type u} [Group X] {V : Type v} [MulAction X V] {Γ : SimpleGraph V}

structure PtLoc (X : Type u) [Group X] {V : Type v} [MulAction X V] (Γ : SimpleGraph V)
    (a b₀ w₀ : V) : Prop where
  dist : Γ.dist a b₀ = 8
  adj : Γ.Adj a w₀
  orb : ∀ b, Γ.dist a b = 8 → ∃ g : X, g • a = a ∧ g • b₀ = b
  trans : ∀ u, Γ.Adj a u → ∃ k : X, k • a = a ∧ k • b₀ = b₀ ∧ k • w₀ = u
  moves : ∀ u, Γ.Adj a u → ∃ k : X, k • a = a ∧ k • b₀ = b₀ ∧ k • u = u ∧
    ∃ w, Γ.Adj a w ∧ k • w ≠ w
  exact : ∃ k : X, k • a = a ∧ k • b₀ = b₀ ∧ k • w₀ = w₀ ∧ ∃ y₀, Γ.Adj b₀ y₀ ∧ k • y₀ = y₀ ∧
    ∀ y, Γ.Adj b₀ y → k • y = y → y = y₀

structure AffLab (X : Type u) [Group X] {V : Type v} [MulAction X V] (Γ : SimpleGraph V)
    (a : V) (lab : ZMod 5 → V) : Prop where
  inj : Function.Injective lab
  adj : ∀ i, Γ.Adj a (lab i)
  surj : ∀ u, Γ.Adj a u → ∃ i, lab i = u
  aff : ∀ g : X, g • a = a → ∃ α β : ZMod 5, α ≠ 0 ∧ ∀ i, g • lab i = lab (α * i + β)

section Arith

theorem arith_tau : ∀ α α' i j : ZMod 5, α ≠ 1 → α' ≠ 1 → i ≠ j →
    (α - 1) * (j - α' * j) - (α' - 1) * (i - α * i) ≠ 0 := by decide

theorem arith_surj : ∀ α α' β β' u : ZMod 5, α ≠ 0 → α' ≠ 0 →
    ∃ s : ZMod 5, α' * (α * s + β) + β' = u := by decide

theorem arith_step : ∀ u u' τ : ZMod 5, τ ≠ 0 → ∃ n : Fin 5, u + ((n : ℕ) : ZMod 5) * τ = u' := by
  decide

end Arith

namespace AffLab

variable {a : V} {lab : ZMod 5 → V} (A : AffLab X Γ a lab)

include A in
theorem pair {g₁ g₂ : X} (h1a : g₁ • a = a) (h2a : g₂ • a = a) {u₁ u₂ : V} (hu₁ : Γ.Adj a u₁)
    (hu₂ : Γ.Adj a u₂) (hne : u₁ ≠ u₂) (h1u : g₁ • u₁ = u₁) (h2u : g₂ • u₂ = u₂)
    (hm1 : ∃ w, Γ.Adj a w ∧ g₁ • w ≠ w) (hm2 : ∃ w, Γ.Adj a w ∧ g₂ • w ≠ w) {y y' : V}
    (hy : Γ.Adj a y) (hy' : Γ.Adj a y') : ∃ g ∈ Subgroup.closure {g₁, g₂}, g • y = y' := by
  obtain ⟨α, β, hα, hg1⟩ := A.aff g₁ h1a
  obtain ⟨α', β', hα', hg2⟩ := A.aff g₂ h2a
  obtain ⟨i, rfl⟩ := A.surj u₁ hu₁
  obtain ⟨j, rfl⟩ := A.surj u₂ hu₂
  have hij : i ≠ j := fun h => hne (by rw [h])
  have hf1 : α * i + β = i := A.inj ((hg1 i).symm.trans h1u)
  have hf2 : α' * j + β' = j := A.inj ((hg2 j).symm.trans h2u)
  have hα1 : α ≠ 1 := by
    intro h1
    obtain ⟨w, hw, hwm⟩ := hm1
    obtain ⟨t, rfl⟩ := A.surj w hw
    subst h1
    have hβ : β = 0 := by linear_combination hf1
    apply hwm
    rw [hg1 t, hβ]
    simp
  have hα1' : α' ≠ 1 := by
    intro h1
    obtain ⟨w, hw, hwm⟩ := hm2
    obtain ⟨t, rfl⟩ := A.surj w hw
    subst h1
    have hβ : β' = 0 := by linear_combination hf2
    apply hwm
    rw [hg2 t, hβ]
    simp
  set τ : ZMod 5 := (α - 1) * β' - (α' - 1) * β with hτ
  have hτ0 : τ ≠ 0 := by
    have hb : β = i - α * i := by linear_combination hf1
    have hb' : β' = j - α' * j := by linear_combination hf2
    rw [hτ, hb, hb']
    exact arith_tau α α' i j hα1 hα1' hij
  set c : X := g₁ * g₂ * g₁⁻¹ * g₂⁻¹ with hc
  have hcm : c ∈ Subgroup.closure {g₁, g₂} := by
    have m1 : g₁ ∈ Subgroup.closure {g₁, g₂} := Subgroup.subset_closure (by simp)
    have m2 : g₂ ∈ Subgroup.closure {g₁, g₂} := Subgroup.subset_closure (by simp)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ m1 m2) (Subgroup.inv_mem _ m1))
      (Subgroup.inv_mem _ m2)
  have hcomm : c * (g₂ * g₁) = g₁ * g₂ := by rw [hc]; group
  have hctr : ∀ u, c • lab u = lab (u + τ) := by
    intro u
    obtain ⟨s, hs⟩ := arith_surj α α' β β' u hα hα'
    have h21 : (g₂ * g₁) • lab s = lab u := by
      rw [mul_smul, hg1 s, hg2, hs]
    have h12 : (g₁ * g₂) • lab s = lab (α * (α' * s + β') + β) := by
      rw [mul_smul, hg2 s, hg1]
    rw [← h21, ← mul_smul, hcomm, h12]
    congr 1
    rw [← hs, hτ]
    ring
  have hpow : ∀ (n : ℕ) (u : ZMod 5), (c ^ n) • lab u = lab (u + (n : ZMod 5) * τ) := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ n ih =>
      intro u
      rw [pow_succ', mul_smul, ih, hctr]
      congr 1
      push_cast
      ring
  obtain ⟨s, rfl⟩ := A.surj y hy
  obtain ⟨s', rfl⟩ := A.surj y' hy'
  obtain ⟨n, hn⟩ := arith_step s s' τ hτ0
  refine ⟨c ^ (n : ℕ), Subgroup.pow_mem _ hcm _, ?_⟩
  rw [hpow, hn]

end AffLab

end CFSG.Quasithin.TitsGeo
