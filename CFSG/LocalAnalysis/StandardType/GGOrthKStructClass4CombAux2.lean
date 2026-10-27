module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermGen

public section

namespace CFSG.StandardType

open CFSG.StandardType.SpJoin

@[expose] noncomputable def okCl_flip (n p : ℕ) (T : Finset (Fin n)) :
    Equiv.Perm (Fin n → Multiplicative (ZMod p)) where
  toFun v := fun t => if t ∈ T then (v t)⁻¹ else v t
  invFun v := fun t => if t ∈ T then (v t)⁻¹ else v t
  left_inv v := by
    funext t
    by_cases h : t ∈ T <;> simp [h]
  right_inv v := by
    funext t
    by_cases h : t ∈ T <;> simp [h]

@[simp] theorem okCl_flip_apply (n p : ℕ) (T : Finset (Fin n))
    (v : Fin n → Multiplicative (ZMod p)) (t : Fin n) :
    okCl_flip n p T v t = if t ∈ T then (v t)⁻¹ else v t := rfl

theorem okCl_flip_mem_spSignedGroup (n p : ℕ) (T : Finset (Fin n)) :
    okCl_flip n p T ∈ spSignedGroup n p := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      have h : okCl_flip n p ∅ = 1 := by
        ext v t
        simp [okCl_flip_apply]
      rw [h]
      exact Subgroup.one_mem _
  | insert a T ha ih =>
      have hstep : okCl_flip n p (insert a T) = coordInv n p a * okCl_flip n p T := by
        ext v t
        rw [okCl_flip_apply, Equiv.Perm.mul_apply, coordInv_apply]
        by_cases ht : t = a
        · subst ht
          simp [Function.update_apply, ha]
        · rw [Function.update_apply, if_neg ht, okCl_flip_apply]
          simp [Finset.mem_insert, ht]
      rw [hstep]
      exact Subgroup.mul_mem _ (coordInv_mem_spSignedGroup a) ih

theorem okCl_coordPerm_mul (n p : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    coordPerm n p (σ * τ) = coordPerm n p σ * coordPerm n p τ := by
  apply Equiv.ext
  intro v
  funext t
  simp only [coordPerm_apply, Equiv.Perm.mul_apply]
  rw [Equiv.Perm.mul_def σ τ, Equiv.symm_trans_apply]

theorem okCl_coordPerm_one (n p : ℕ) :
    coordPerm n p (1 : Equiv.Perm (Fin n)) = 1 := by
  apply Equiv.ext
  intro v
  funext t
  simp only [coordPerm_apply, Equiv.Perm.one_symm, Equiv.Perm.one_apply]

theorem okCl_coordPerm_inv (n p : ℕ) (σ : Equiv.Perm (Fin n)) :
    coordPerm n p σ⁻¹ = (coordPerm n p σ)⁻¹ := by
  apply Equiv.ext
  intro v
  funext t
  rw [coordPerm_apply, Equiv.Perm.inv_def, Equiv.symm_symm]
  rfl

theorem okCl_coordPerm_injective (n : ℕ) : Function.Injective (coordPerm n 3) := by
  intro σ τ h
  have hfun : ∀ (v : Fin n → Multiplicative (ZMod 3)) (t : Fin n),
      coordPerm n 3 σ v t = coordPerm n 3 τ v t :=
    fun v t => congrArg (fun e : Equiv.Perm (Fin n → Multiplicative (ZMod 3)) => e v t) h
  apply Equiv.ext
  intro j
  have h1 : Multiplicative.ofAdd (1 : ZMod 3) ≠ (1 : Multiplicative (ZMod 3)) := by decide
  have key := hfun (Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod 3))) (σ j)
  rw [coordPerm_apply, coordPerm_apply, Equiv.symm_apply_apply, Pi.mulSingle_apply,
    Pi.mulSingle_apply] at key
  by_cases hτ : τ.symm (σ j) = j
  · have := congrArg τ hτ
    rw [Equiv.apply_symm_apply] at this
    exact this
  · rw [if_pos rfl, if_neg hτ] at key
    exact absurd key h1

theorem okCl_coordPerm_conj (n p : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    (⟨coordPerm n p σ, coordPerm_mem_spSignedGroup σ⟩ : spSignedGroup n p) *
        ⟨coordPerm n p τ, coordPerm_mem_spSignedGroup τ⟩ *
        (⟨coordPerm n p σ, coordPerm_mem_spSignedGroup σ⟩ : spSignedGroup n p)⁻¹ =
      ⟨coordPerm n p (σ * τ * σ⁻¹), coordPerm_mem_spSignedGroup _⟩ := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [okCl_coordPerm_mul, ← okCl_coordPerm_inv, okCl_coordPerm_mul]

end CFSG.StandardType

end
