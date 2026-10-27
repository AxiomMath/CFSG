module

public import CFSG.RankThree.PartOne.U4F.Cases

public section

namespace CFSG.RankThree.PartOne.U4F

open Matrix CFSG CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne.KFU

variable {K : Type} [Field K]

structure Config (σ : K ≃+* K) (r : ℕ) (A B : Subgroup ↥(SU σ 4)) (ρ τ : ↥(SU σ 4)) : Prop where
  perfA : Group.IsPerfect ↥A
  perfB : Group.IsPerfect ↥B
  cardA : Nat.card ↥A = Nat.card (SpecialLinearGroup (Fin 2) K)
  cardB : Nat.card ↥B = Nat.card (SpecialLinearGroup (Fin 2) (fixF σ))
  rho_mem : ρ ∈ A
  tau_mem : τ ∈ B
  rho_pow : ρ ^ r = 1
  tau_pow : τ ^ r = 1
  rho_ne : ρ ≠ 1
  tau_ne : τ ≠ 1
  comm : ρ * τ = τ * ρ
  inter : ∀ i j : ℕ, ρ ^ i = τ ^ j → ρ ^ i = 1
  gamma₁ : ∃ γ ∈ Subgroup.closure {ρ, τ}, γ ≠ 1 ∧ ∀ a ∈ A, a * γ = γ * a
  gamma₂ : ∃ γ ∈ Subgroup.closure {ρ, τ}, γ ≠ 1 ∧ ∀ b ∈ B, b * γ = γ * b
  std : ∃ a ∈ A, τ * a ≠ a * τ

variable {σ : K ≃+* K} {r : ℕ} {A B : Subgroup ↥(SU σ 4)} {ρ τ : ↥(SU σ 4)}

theorem conj_mem_closure_pair (g : ↥(SU σ 4)) {γ : ↥(SU σ 4)} (hγ : γ ∈ Subgroup.closure {ρ, τ}) :
    g * γ * g⁻¹ ∈ Subgroup.closure {g * ρ * g⁻¹, g * τ * g⁻¹} := by
  have h := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hγ
  rw [MonoidHom.map_closure, Set.image_pair] at h
  exact h

theorem Config.conj (c : Config σ r A B ρ τ) (g : ↥(SU σ 4)) :
    Config σ r (A.map (MulAut.conj g).toMonoidHom) (B.map (MulAut.conj g).toMonoidHom)
      (g * ρ * g⁻¹) (g * τ * g⁻¹) where
  perfA := isPerfect_map_conj c.perfA g
  perfB := isPerfect_map_conj c.perfB g
  cardA := by
    rw [← c.cardA]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective A (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv).symm
  cardB := by
    rw [← c.cardB]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective B (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv).symm
  rho_mem := ⟨ρ, c.rho_mem, rfl⟩
  tau_mem := ⟨τ, c.tau_mem, rfl⟩
  rho_pow := by
    rw [conj_pow, c.rho_pow, mul_one, mul_inv_cancel]
  tau_pow := by
    rw [conj_pow, c.tau_pow, mul_one, mul_inv_cancel]
  rho_ne := fun h => c.rho_ne (by simpa using h)
  tau_ne := fun h => c.tau_ne (by simpa using h)
  comm := by
    calc g * ρ * g⁻¹ * (g * τ * g⁻¹) = g * (ρ * τ) * g⁻¹ := by group
      _ = g * (τ * ρ) * g⁻¹ := by rw [c.comm]
      _ = g * τ * g⁻¹ * (g * ρ * g⁻¹) := by group
  inter := by
    intro i j h
    have h' : ρ ^ i = τ ^ j := by
      have := congrArg (fun x => g⁻¹ * x * g) h
      simpa [conj_pow] using this
    have := c.inter i j h'
    rw [conj_pow, this]
    group
  gamma₁ := by
    obtain ⟨γ, hγ, hγ1, hγc⟩ := c.gamma₁
    refine ⟨g * γ * g⁻¹, conj_mem_closure_pair g hγ, fun h => hγ1 (by simpa using h), ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    show g * a * g⁻¹ * (g * γ * g⁻¹) = g * γ * g⁻¹ * (g * a * g⁻¹)
    calc g * a * g⁻¹ * (g * γ * g⁻¹) = g * (a * γ) * g⁻¹ := by group
      _ = g * (γ * a) * g⁻¹ := by rw [hγc a ha]
      _ = _ := by group
  gamma₂ := by
    obtain ⟨γ, hγ, hγ1, hγc⟩ := c.gamma₂
    refine ⟨g * γ * g⁻¹, conj_mem_closure_pair g hγ, fun h => hγ1 (by simpa using h), ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    show g * b * g⁻¹ * (g * γ * g⁻¹) = g * γ * g⁻¹ * (g * b * g⁻¹)
    calc g * b * g⁻¹ * (g * γ * g⁻¹) = g * (b * γ) * g⁻¹ := by group
      _ = g * (γ * b) * g⁻¹ := by rw [hγc b hb]
      _ = _ := by group
  std := by
    obtain ⟨a, ha, hne⟩ := c.std
    refine ⟨g * a * g⁻¹, ⟨a, ha, rfl⟩, fun h => hne ?_⟩
    have h2 : g * (τ * a) * g⁻¹ = g * (a * τ) * g⁻¹ := by
      calc g * (τ * a) * g⁻¹ = g * τ * g⁻¹ * (g * a * g⁻¹) := by group
        _ = g * a * g⁻¹ * (g * τ * g⁻¹) := h
        _ = g * (a * τ) * g⁻¹ := by group
    simpa using h2

end CFSG.RankThree.PartOne.U4F
