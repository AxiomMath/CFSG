module

public import Mathlib.Algebra.Group.End
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

variable {V : Type*} [Group V]

theorem eq_one_of_eq_inv (h3 : ∀ v : V, v ^ 3 = 1) {v : V} (h : v = v⁻¹) : v = 1 := by
  have h2 : v * v = 1 := by
    calc v * v = v * v⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel v
  calc v = v ^ 3 * (v * v)⁻¹ := by rw [pow_three]; group
    _ = 1 := by rw [h3, h2]; group

theorem eq_one_of_conj_mem_four (h3 : ∀ v : V, v ^ 3 = 1) {σ₁ σ₂ β : MulAut V}
    (hσ₂ : ∀ v, σ₂ v = (σ₁ v)⁻¹) (hβ3 : β ^ 3 = 1)
    (hD : β * σ₁ * β⁻¹ = 1 ∨ β * σ₁ * β⁻¹ = σ₁ ∨ β * σ₁ * β⁻¹ = σ₂ ∨
      ∀ v, (β * σ₁ * β⁻¹) v = v⁻¹)
    {w w' : V} (hw : σ₁ w = w) (hw1 : w ≠ 1) (hfix : ∀ v, σ₁ v = v → v = 1 ∨ v = w ∨ v = w⁻¹)
    (hw' : σ₂ w' = w') (hw'1 : w' ≠ 1) (hfix' : ∀ v, σ₂ v = v → v = 1 ∨ v = w' ∨ v = w'⁻¹)
    (hgen : ∀ v, ∃ a b : ℕ, v = w' ^ a * w ^ b) : β = 1 := by
  have hσ₁w' : σ₁ w' = w'⁻¹ := by
    have := hw'
    rw [hσ₂] at this
    exact inv_eq_iff_eq_inv.mp this
  have hne' : w'⁻¹ ≠ w' := fun h => hw'1 (eq_one_of_eq_inv h3 h.symm)
  have hσ₁1 : σ₁ ≠ 1 := fun h => hne' (by rw [← hσ₁w', h, MulAut.one_apply])
  have hσ₁₂ : σ₁ ≠ σ₂ := fun h => hne' (by rw [← hσ₁w', h, hw'])
  have hβw1 : β w ≠ 1 := fun h => hw1 (by rw [← map_one β] at h; exact β.injective h)
  have hfixβ : (β * σ₁ * β⁻¹) (β w) = β w := by
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, hw]
  have hcases : β * σ₁ * β⁻¹ = σ₁ ∨ β * σ₁ * β⁻¹ = σ₂ := by
    rcases hD with h | h | h | h
    · exfalso
      apply hσ₁1
      have e : σ₁ = β⁻¹ * (β * σ₁ * β⁻¹) * β := by group
      rw [e, h]; group
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have := h (β w)
      rw [hfixβ] at this
      exact hβw1 (eq_one_of_eq_inv h3 this)
  have hβσ₂ : ∀ τ : MulAut V, β * σ₁ * β⁻¹ = τ → ∀ v, (β * σ₂ * β⁻¹) v = (τ v)⁻¹ := by
    intro τ hτ v
    rw [← hτ]
    simp only [MulAut.mul_apply, hσ₂, map_inv]
  have hcomm : β * σ₁ * β⁻¹ = σ₁ := by
    rcases hcases with h | h
    · exact h
    · exfalso
      have h2 : β * σ₂ * β⁻¹ = σ₁ := by
        ext v
        rw [hβσ₂ σ₂ h v, hσ₂, inv_inv]
      have hb : β * β * β = 1 := by rw [← hβ3, pow_three, mul_assoc]
      apply hσ₁₂
      calc σ₁ = (β * β * β) * σ₁ * (β * β * β)⁻¹ := by rw [hb]; group
        _ = β * (β * (β * σ₁ * β⁻¹) * β⁻¹) * β⁻¹ := by group
        _ = σ₂ := by rw [h, h2, h]
  have hβσ₁ : ∀ v, β (σ₁ v) = σ₁ (β v) := by
    intro v
    have := congrArg (fun f : MulAut V => f (β v)) hcomm
    simpa [MulAut.mul_apply] using this
  have hβσ₂' : ∀ v, β (σ₂ v) = σ₂ (β v) := by
    intro v
    rw [hσ₂, hσ₂, map_inv, hβσ₁]
  have key : ∀ (σ : MulAut V) (u : V), σ u = u → u ≠ 1 →
      (∀ v, σ v = v → v = 1 ∨ v = u ∨ v = u⁻¹) → (∀ v, β (σ v) = σ (β v)) → β u = u := by
    intro σ u hu hu1 hfx hβσ
    have hβu : σ (β u) = β u := by rw [← hβσ, hu]
    rcases hfx (β u) hβu with h | h | h
    · exact absurd (by rw [← map_one β] at h; exact β.injective h) hu1
    · exact h
    · exfalso
      have hβ3u : (β ^ 3) u = u⁻¹ := by
        simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, h, map_inv, inv_inv]
      rw [hβ3, MulAut.one_apply] at hβ3u
      exact hu1 (eq_one_of_eq_inv h3 hβ3u)
  have hβw : β w = w := key σ₁ w hw hw1 hfix hβσ₁
  have hβw' : β w' = w' := key σ₂ w' hw' hw'1 hfix' hβσ₂'
  ext v
  obtain ⟨a, b, rfl⟩ := hgen v
  rw [map_mul, map_pow, map_pow, hβw, hβw', MulAut.one_apply]

end CFSG.Quasithin.Vol2.Ch10.SecB.E9
