module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneTorusDefs

public section

namespace CFSG.StandardType.SpJoin

theorem spRefl_involutive (n p : ℕ) (k : Fin n) : Function.Involutive (spRefl n p k) := by
  intro f
  by_cases hk : k.val + 1 < n
  · funext i
    simp only [spRefl, dif_pos hk, Equiv.swap_apply_self]
  · funext i
    simp only [spRefl, dif_neg hk]
    by_cases hik : i = k
    · subst hik
      simp
    · simp [Function.update_of_ne hik]

@[expose] def coordPerm (n p : ℕ) (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin n → Multiplicative (ZMod p)) where
  toFun v := fun t => v (σ.symm t)
  invFun v := fun t => v (σ t)
  left_inv v := by funext t; simp
  right_inv v := by funext t; simp

@[simp] theorem coordPerm_apply (n p : ℕ) (σ : Equiv.Perm (Fin n))
    (v : Fin n → Multiplicative (ZMod p)) (t : Fin n) : coordPerm n p σ v t = v (σ.symm t) := rfl

@[expose] def coordInv (n p : ℕ) (i : Fin n) : Equiv.Perm (Fin n → Multiplicative (ZMod p)) where
  toFun v := Function.update v i (v i)⁻¹
  invFun v := Function.update v i (v i)⁻¹
  left_inv v := by funext t; by_cases h : t = i <;> simp [Function.update_apply, h]
  right_inv v := by funext t; by_cases h : t = i <;> simp [Function.update_apply, h]

@[simp] theorem coordInv_apply (n p : ℕ) (i : Fin n) (v : Fin n → Multiplicative (ZMod p)) :
    coordInv n p i v = Function.update v i (v i)⁻¹ := rfl

@[expose] def spReflPerm (n p : ℕ) (k : Fin n) : Equiv.Perm (Fin n → Multiplicative (ZMod p)) :=
  (spRefl_involutive n p k).toPerm _

@[simp] theorem spReflPerm_apply (n p : ℕ) (k : Fin n) (v : Fin n → Multiplicative (ZMod p)) :
    spReflPerm n p k v = spRefl n p k v := rfl

theorem spReflPerm_of_lt (n p : ℕ) (k : Fin n) (hk : k.val + 1 < n) :
    spReflPerm n p k = coordPerm n p (Equiv.swap k ⟨k.val + 1, hk⟩) := by
  ext v t
  simp only [spReflPerm_apply, spRefl, dif_pos hk, coordPerm_apply, Equiv.symm_swap]

theorem spReflPerm_of_not_lt (n p : ℕ) (k : Fin n) (hk : ¬ k.val + 1 < n) :
    spReflPerm n p k = coordInv n p k := by
  ext v t
  simp only [spReflPerm_apply, spRefl, dif_neg hk, coordInv_apply]

@[expose] def spSignedGroup (n p : ℕ) : Subgroup (Equiv.Perm (Fin n → Multiplicative (ZMod p))) :=
  Subgroup.closure (Set.range (spReflPerm n p))

theorem spReflPerm_mem_spSignedGroup (n p : ℕ) (k : Fin n) :
    spReflPerm n p k ∈ spSignedGroup n p :=
  Subgroup.subset_closure ⟨k, rfl⟩

end CFSG.StandardType.SpJoin
