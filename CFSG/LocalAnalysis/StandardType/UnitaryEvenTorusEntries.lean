module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Fintype.Basic

public section

namespace CFSG.StandardType

namespace UnitaryEvenTorus

variable {F : Type*} [Field F]

@[expose] def torusEntry {n m : ℕ} (μ : Subgroup Fˣ) (a : Fin m → μ) (j : Fin n) : Fˣ :=
  if h : j.val < m then (a ⟨j.val, h⟩ : Fˣ)
  else if h' : (Fin.rev j).val < m then ((a ⟨(Fin.rev j).val, h'⟩ : Fˣ))⁻¹ else 1

theorem torusEntry_of_lt {n m : ℕ} (μ : Subgroup Fˣ) (a : Fin m → μ) {j : Fin n} (h : j.val < m) :
    torusEntry μ a j = (a ⟨j.val, h⟩ : Fˣ) := by
  rw [torusEntry, dif_pos h]

theorem torusEntry_of_rev_lt {n m : ℕ} (μ : Subgroup Fˣ) (a : Fin m → μ) {j : Fin n}
    (h : ¬ j.val < m) (h' : (Fin.rev j).val < m) :
    torusEntry μ a j = ((a ⟨(Fin.rev j).val, h'⟩ : Fˣ))⁻¹ := by
  rw [torusEntry, dif_neg h, dif_pos h']

theorem torusEntry_of_not {n m : ℕ} (μ : Subgroup Fˣ) (a : Fin m → μ) {j : Fin n}
    (h : ¬ j.val < m) (h' : ¬ (Fin.rev j).val < m) :
    torusEntry μ a j = 1 := by
  rw [torusEntry, dif_neg h, dif_neg h']

theorem torusEntry_mem {n m : ℕ} (μ : Subgroup Fˣ) (a : Fin m → μ) (j : Fin n) :
    torusEntry μ a j ∈ μ := by
  by_cases h : j.val < m
  · rw [torusEntry_of_lt μ a h]
    exact (a ⟨j.val, h⟩).2
  · by_cases h' : (Fin.rev j).val < m
    · rw [torusEntry_of_rev_lt μ a h h']
      exact μ.inv_mem (a ⟨(Fin.rev j).val, h'⟩).2
    · rw [torusEntry_of_not μ a h h']
      exact μ.one_mem

theorem torusEntry_one {n m : ℕ} (μ : Subgroup Fˣ) (j : Fin n) :
    torusEntry μ (1 : Fin m → μ) j = 1 := by
  by_cases h : j.val < m
  · rw [torusEntry_of_lt μ 1 h]; simp
  · by_cases h' : (Fin.rev j).val < m
    · rw [torusEntry_of_rev_lt μ 1 h h']; simp
    · rw [torusEntry_of_not μ 1 h h']

theorem torusEntry_mul {n m : ℕ} (μ : Subgroup Fˣ) (a b : Fin m → μ) (j : Fin n) :
    torusEntry μ (a * b) j = torusEntry μ a j * torusEntry μ b j := by
  by_cases h : j.val < m
  · rw [torusEntry_of_lt μ (a * b) h, torusEntry_of_lt μ a h, torusEntry_of_lt μ b h]
    simp [Subgroup.coe_mul]
  · by_cases h' : (Fin.rev j).val < m
    · rw [torusEntry_of_rev_lt μ (a * b) h h', torusEntry_of_rev_lt μ a h h',
        torusEntry_of_rev_lt μ b h h']
      simp only [Pi.mul_apply, Subgroup.coe_mul, mul_inv]
    · rw [torusEntry_of_not μ (a * b) h h', torusEntry_of_not μ a h h',
        torusEntry_of_not μ b h h']
      simp

@[expose] def entryHom (n : ℕ) {m : ℕ} (μ : Subgroup Fˣ) : (Fin m → μ) →* (Fin n → Fˣ) where
  toFun a := fun j => torusEntry μ a j
  map_one' := funext (torusEntry_one μ)
  map_mul' a b := funext (torusEntry_mul μ a b)

theorem entryHom_apply (n : ℕ) {m : ℕ} (μ : Subgroup Fˣ) (a : Fin m → μ) (j : Fin n) :
    entryHom n μ a j = torusEntry μ a j :=
  rfl

theorem entryHom_injective (n : ℕ) {m : ℕ} (μ : Subgroup Fˣ) (hmn : m ≤ n) :
    Function.Injective (entryHom n μ : (Fin m → μ) →* (Fin n → Fˣ)) := by
  intro a b h
  funext k
  apply Subtype.ext
  have hk : k.val < n := lt_of_lt_of_le k.isLt hmn
  have h' := congrFun h ⟨k.val, hk⟩
  simp only [entryHom_apply] at h'
  rw [torusEntry_of_lt μ a (j := ⟨k.val, hk⟩) k.isLt,
    torusEntry_of_lt μ b (j := ⟨k.val, hk⟩) k.isLt] at h'
  simpa using h'

theorem torusEntry_mul_rev {n m : ℕ} (μ : Subgroup Fˣ) (h2m : 2 * m ≤ n) (a : Fin m → μ)
    (j : Fin n) :
    torusEntry μ a j * torusEntry μ a (Fin.rev j) = 1 := by
  by_cases h : j.val < m
  · have hrevnot : ¬ (Fin.rev j).val < m := by
      rw [Fin.val_rev]
      omega
    have hjj : (Fin.rev (Fin.rev j)).val < m := by simpa using h
    rw [torusEntry_of_lt μ a h, torusEntry_of_rev_lt μ a hrevnot hjj]
    have key : (⟨(Fin.rev (Fin.rev j)).val, hjj⟩ : Fin m) = ⟨j.val, h⟩ := by
      ext
      simp
    rw [key, mul_inv_cancel]
  · by_cases h' : (Fin.rev j).val < m
    · rw [torusEntry_of_rev_lt μ a h h', torusEntry_of_lt μ a h', inv_mul_cancel]
    · have hjjnot : ¬ (Fin.rev (Fin.rev j)).val < m := by simpa using h
      rw [torusEntry_of_not μ a h h', torusEntry_of_not μ a h' hjjnot, mul_one]

theorem prod_torusEntry {n m : ℕ} (μ : Subgroup Fˣ) (h2m : 2 * m ≤ n) (hμ : ∀ x ∈ μ, x ^ 3 = 1)
    (a : Fin m → μ) : ∏ j : Fin n, torusEntry μ a j = 1 := by
  let e : Fin n → Fˣ := fun j => torusEntry μ a j
  change ∏ j : Fin n, e j = 1
  have he_mem : ∀ j, e j ∈ μ := fun j => torusEntry_mem μ a j
  have h3 : (∏ j : Fin n, e j) ^ 3 = 1 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_eq_one (fun j _ => hμ (e j) (he_mem j))
  have hrev : (∏ j : Fin n, e (Fin.rev j)) = ∏ j : Fin n, e j := by
    simpa using (Equiv.prod_comp (Fin.revPerm : Equiv.Perm (Fin n)) e)
  have h2 : (∏ j : Fin n, e j) * (∏ j : Fin n, e j) = 1 := by
    calc (∏ j : Fin n, e j) * (∏ j : Fin n, e j)
        = (∏ j : Fin n, e j) * (∏ j : Fin n, e (Fin.rev j)) := by rw [hrev]
      _ = ∏ j : Fin n, e j * e (Fin.rev j) := by rw [← Finset.prod_mul_distrib]
      _ = 1 := Finset.prod_eq_one (fun j _ => torusEntry_mul_rev μ h2m a j)
  calc (∏ j : Fin n, e j)
      = (∏ j : Fin n, e j) ^ 3 * ((∏ j : Fin n, e j) * (∏ j : Fin n, e j))⁻¹ := by group
    _ = 1 := by rw [h3, h2]; simp

end UnitaryEvenTorus

end CFSG.StandardType
