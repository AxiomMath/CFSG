module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermBase

public section

namespace CFSG.StandardType

open CFSG.StandardType.SpJoin

@[expose] def okCl_IsSigned (n p : ℕ)
    (g : Equiv.Perm (Fin n → Multiplicative (ZMod p))) : Prop :=
  ∃ (σ : Equiv.Perm (Fin n)) (s : Fin n → Bool),
    ∀ (v : Fin n → Multiplicative (ZMod p)) (j : Fin n),
      g v (σ j) = if s j then (v j)⁻¹ else v j

theorem okCl_IsSigned_one (n p : ℕ) : okCl_IsSigned n p 1 := by
  refine ⟨1, fun _ => false, ?_⟩
  intro v j
  rw [Equiv.Perm.one_apply]
  simp

theorem okCl_IsSigned_gen (n p : ℕ) (i : Fin n) :
    okCl_IsSigned n p (spReflPerm n p i) := by
  by_cases hi : i.val + 1 < n
  · refine ⟨Equiv.swap i ⟨i.val + 1, hi⟩, fun _ => false, ?_⟩
    intro v j
    rw [spReflPerm_of_lt n p i hi]
    simp [coordPerm_apply]
  · refine ⟨1, fun j => decide (j = i), ?_⟩
    intro v j
    rw [spReflPerm_of_not_lt n p i hi, Equiv.Perm.one_apply, coordInv_apply]
    by_cases hji : j = i
    · subst hji
      simp [Function.update_apply]
    · simp [Function.update_apply, hji]

theorem okCl_IsSigned_mul {n p : ℕ} {g₁ g₂ : Equiv.Perm (Fin n → Multiplicative (ZMod p))}
    (h₁ : okCl_IsSigned n p g₁) (h₂ : okCl_IsSigned n p g₂) :
    okCl_IsSigned n p (g₁ * g₂) := by
  obtain ⟨σ₁, s₁, h₁⟩ := h₁
  obtain ⟨σ₂, s₂, h₂⟩ := h₂
  refine ⟨σ₁ * σ₂, fun j => Bool.xor (s₁ (σ₂ j)) (s₂ j), ?_⟩
  intro v j
  simp only [Equiv.Perm.mul_apply]
  rw [h₁ (g₂ v) (σ₂ j), h₂ v j]
  by_cases hA : s₁ (σ₂ j) <;> by_cases hB : s₂ j <;> simp [hA, hB, Bool.xor]

theorem okCl_IsSigned_inv {n p : ℕ} {g : Equiv.Perm (Fin n → Multiplicative (ZMod p))}
    (h : okCl_IsSigned n p g) : okCl_IsSigned n p g⁻¹ := by
  obtain ⟨σ, s, h⟩ := h
  refine ⟨σ⁻¹, fun j => s (σ.symm j), ?_⟩
  intro v j
  change g⁻¹ v (σ.symm j) = if s (σ.symm j) then (v j)⁻¹ else v j
  have hgv : g (g⁻¹ v) = v := by
    rw [Equiv.Perm.inv_def]
    exact Equiv.apply_symm_apply g v
  have key := h (g⁻¹ v) (σ.symm j)
  rw [hgv, Equiv.apply_symm_apply] at key
  by_cases hA : s (σ.symm j)
  · rw [if_pos hA] at key
    rw [if_pos hA]
    rw [key, inv_inv]
  · rw [if_neg hA] at key
    rw [if_neg hA]
    exact key.symm

theorem okCl_IsSigned_closure (n p : ℕ) {g : Equiv.Perm (Fin n → Multiplicative (ZMod p))}
    (hg : g ∈ spSignedGroup n p) : okCl_IsSigned n p g := by
  refine Subgroup.closure_induction (k := Set.range (spReflPerm n p))
    (p := fun x _ => okCl_IsSigned n p x) ?_ ?_ ?_ ?_ hg
  · rintro x ⟨i, rfl⟩
    exact okCl_IsSigned_gen n p i
  · exact okCl_IsSigned_one n p
  · intro x y _ _ hx hy
    exact okCl_IsSigned_mul hx hy
  · intro x _ hx
    exact okCl_IsSigned_inv hx

end CFSG.StandardType

end
