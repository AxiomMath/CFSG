module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

@[expose] def s16t3AltN0 (n : ℕ) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {σ | ∀ i : Fin n, (σ i : ℕ) / 4 = (i : ℕ) / 4}
  mul_mem' := fun {σ τ} hσ hτ i => by
    rw [Equiv.Perm.mul_apply]
    exact (hσ (τ i)).trans (hτ i)
  one_mem' := fun i => rfl
  inv_mem' := fun {σ} hσ i => by
    have h := hσ (σ⁻¹ i)
    have e : σ (σ⁻¹ i) = i := by simp
    rw [e] at h
    exact h.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
