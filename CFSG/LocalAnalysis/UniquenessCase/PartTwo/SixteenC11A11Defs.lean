module

public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Equiv
open scoped Pointwise

@[expose] def s16c11A11Set3 : Set (Fin 11) := {8, 9, 10}

@[expose] def s16c11A11Pres : Subgroup (Perm (Fin 11)) :=
  MulAction.stabilizer (Perm (Fin 11)) s16c11A11Set3

@[expose] def S16C11A11Blk (σ : Perm (Fin 11)) : Prop :=
  ∀ i j : Fin 11, (i : ℕ) < 8 → (j : ℕ) < 8 →
    (((i : ℕ) / 4 = (j : ℕ) / 4 ↔ ((σ i : Fin 11) : ℕ) / 4 = ((σ j : Fin 11) : ℕ) / 4) ∧
      ((i : ℕ) / 2 = (j : ℕ) / 2 ↔ ((σ i : Fin 11) : ℕ) / 2 = ((σ j : Fin 11) : ℕ) / 2))

instance (σ : Perm (Fin 11)) : Decidable (S16C11A11Blk σ) := by
  unfold S16C11A11Blk
  infer_instance

theorem s16c11A11_mem_pres_iff {σ : Perm (Fin 11)} :
    σ ∈ s16c11A11Pres ↔ ∀ i : Fin 11, ((σ i : Fin 11) : ℕ) < 8 ↔ (i : ℕ) < 8 := by
  rw [s16c11A11Pres, MulAction.mem_stabilizer_set]
  have hmem : ∀ a : Fin 11, a ∈ s16c11A11Set3 ↔ ¬ (a : ℕ) < 8 := by
    intro a
    simp only [s16c11A11Set3, Set.mem_insert_iff, Set.mem_singleton_iff]
    revert a
    decide
  constructor
  · intro h i
    have h1 := h i
    rw [Perm.smul_def, hmem, hmem] at h1
    omega
  · intro h i
    rw [Perm.smul_def, hmem, hmem]
    have h1 := h i
    omega

@[expose] def s16c11A11Full : Subgroup (Perm (Fin 11)) where
  carrier := {σ | σ ∈ s16c11A11Pres ∧ S16C11A11Blk σ}
  mul_mem' := by
    rintro σ τ ⟨hσP, hσB⟩ ⟨hτP, hτB⟩
    refine ⟨s16c11A11Pres.mul_mem hσP hτP, ?_⟩
    intro i j hi hj
    have hτi := (s16c11A11_mem_pres_iff.1 hτP i).2 hi
    have hτj := (s16c11A11_mem_pres_iff.1 hτP j).2 hj
    have h1 := hτB i j hi hj
    have h2 := hσB (τ i) (τ j) hτi hτj
    simp only [Perm.mul_apply]
    exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
  one_mem' := by
    refine ⟨s16c11A11Pres.one_mem, ?_⟩
    intro i j _ _
    simp
  inv_mem' := by
    rintro σ ⟨hσP, hσB⟩
    refine ⟨s16c11A11Pres.inv_mem hσP, ?_⟩
    intro i j hi hj
    have hi' := (s16c11A11_mem_pres_iff.1 (s16c11A11Pres.inv_mem hσP) i).2 hi
    have hj' := (s16c11A11_mem_pres_iff.1 (s16c11A11Pres.inv_mem hσP) j).2 hj
    have h := hσB (σ⁻¹ i) (σ⁻¹ j) hi' hj'
    simp only [Perm.inv_def, Equiv.apply_symm_apply] at h
    exact ⟨h.1.symm, h.2.symm⟩

@[expose] def s16c11A11Y : Subgroup (Perm (Fin 11)) :=
  s16c11A11Full ⊓ alternatingGroup (Fin 11)

@[expose] def s16c11A11T : Subgroup (Perm (Fin 11)) :=
  s16c11A11Y ⊓ MulAction.stabilizer (Perm (Fin 11)) (10 : Fin 11)

@[expose] def s16c11A11Low : Subgroup (Perm (Fin 11)) :=
  MulAction.stabilizer (Perm (Fin 11)) (8 : Fin 11) ⊓
    MulAction.stabilizer (Perm (Fin 11)) (9 : Fin 11) ⊓
    MulAction.stabilizer (Perm (Fin 11)) (10 : Fin 11)

@[expose] def s16c11A11K : Subgroup (Perm (Fin 11)) :=
  s16c11A11Y ⊓ s16c11A11Low

theorem s16c11A11_Y_le_alt : s16c11A11Y ≤ alternatingGroup (Fin 11) := inf_le_right

theorem s16c11A11_Y_le_pres : s16c11A11Y ≤ s16c11A11Pres := fun _ h => h.1.1

theorem s16c11A11_T_le_Y : s16c11A11T ≤ s16c11A11Y := inf_le_left

theorem s16c11A11_T_le_alt : s16c11A11T ≤ alternatingGroup (Fin 11) :=
  s16c11A11_T_le_Y.trans s16c11A11_Y_le_alt

theorem s16c11A11_K_le_Y : s16c11A11K ≤ s16c11A11Y := inf_le_left

theorem s16c11A11_K_le_T : s16c11A11K ≤ s16c11A11T := by
  intro σ hσ
  exact ⟨hσ.1, hσ.2.2⟩

@[expose] def s16c11A11m1 : Perm (Fin 11) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7

@[expose] def s16c11A11m2 : Perm (Fin 11) := swap 0 2 * swap 1 3 * swap 4 6 * swap 5 7

@[expose] def s16c11A11m3 : Perm (Fin 11) := swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7

@[expose] def s16c11A11u : Perm (Fin 11) := swap 0 1 * swap 8 9

@[expose] def s16c11A11k1 : Perm (Fin 11) := swap 2 3 * swap 6 7

@[expose] def s16c11A11k2 : Perm (Fin 11) := swap 0 2 * swap 1 3

@[expose] def s16c11A11c : Perm (Fin 11) := swap 8 9 * swap 9 10

theorem s16c11A11_mem_Y_iff {σ : Perm (Fin 11)} :
    σ ∈ s16c11A11Y ↔ (σ ∈ s16c11A11Pres ∧ S16C11A11Blk σ) ∧ Perm.sign σ = 1 :=
  Iff.rfl

theorem s16c11A11_mem_T_iff {σ : Perm (Fin 11)} :
    σ ∈ s16c11A11T ↔ ((σ ∈ s16c11A11Pres ∧ S16C11A11Blk σ) ∧ Perm.sign σ = 1) ∧ σ 10 = 10 :=
  Iff.rfl

theorem s16c11A11_mem_K_iff {σ : Perm (Fin 11)} :
    σ ∈ s16c11A11K ↔ ((σ ∈ s16c11A11Pres ∧ S16C11A11Blk σ) ∧ Perm.sign σ = 1) ∧
      (σ 8 = 8 ∧ σ 9 = 9) ∧ σ 10 = 10 :=
  Iff.rfl

theorem s16c11A11_m1_mem_T : s16c11A11m1 ∈ s16c11A11T := by
  refine s16c11A11_mem_T_iff.2 ⟨⟨⟨s16c11A11_mem_pres_iff.2 (by decide), by decide⟩, ?_⟩, by decide⟩
  simp [s16c11A11m1, Perm.sign_mul, Perm.sign_swap']

theorem s16c11A11_m2_mem_T : s16c11A11m2 ∈ s16c11A11T := by
  refine s16c11A11_mem_T_iff.2 ⟨⟨⟨s16c11A11_mem_pres_iff.2 (by decide), by decide⟩, ?_⟩, by decide⟩
  simp [s16c11A11m2, Perm.sign_mul, Perm.sign_swap']

theorem s16c11A11_m3_mem_T : s16c11A11m3 ∈ s16c11A11T := by
  refine s16c11A11_mem_T_iff.2 ⟨⟨⟨s16c11A11_mem_pres_iff.2 (by decide), by decide⟩, ?_⟩, by decide⟩
  simp [s16c11A11m3, Perm.sign_mul, Perm.sign_swap']

theorem s16c11A11_u_mem_T : s16c11A11u ∈ s16c11A11T := by
  refine s16c11A11_mem_T_iff.2 ⟨⟨⟨s16c11A11_mem_pres_iff.2 (by decide), by decide⟩, ?_⟩, by decide⟩
  simp [s16c11A11u, Perm.sign_mul, Perm.sign_swap']

theorem s16c11A11_k1_mem_K : s16c11A11k1 ∈ s16c11A11K := by
  refine s16c11A11_mem_K_iff.2 ⟨⟨⟨s16c11A11_mem_pres_iff.2 (by decide), by decide⟩, ?_⟩,
    ⟨by decide, by decide⟩, by decide⟩
  simp [s16c11A11k1, Perm.sign_mul, Perm.sign_swap']

theorem s16c11A11_k2_mem_K : s16c11A11k2 ∈ s16c11A11K := by
  refine s16c11A11_mem_K_iff.2 ⟨⟨⟨s16c11A11_mem_pres_iff.2 (by decide), by decide⟩, ?_⟩,
    ⟨by decide, by decide⟩, by decide⟩
  simp [s16c11A11k2, Perm.sign_mul, Perm.sign_swap']

theorem s16c11A11_m3_mem_K : s16c11A11m3 ∈ s16c11A11K := by
  refine s16c11A11_mem_K_iff.2 ⟨⟨⟨s16c11A11_mem_pres_iff.2 (by decide), by decide⟩, ?_⟩,
    ⟨by decide, by decide⟩, by decide⟩
  simp [s16c11A11m3, Perm.sign_mul, Perm.sign_swap']

theorem s16c11A11_c_mem_Y : s16c11A11c ∈ s16c11A11Y := by
  refine s16c11A11_mem_Y_iff.2 ⟨⟨s16c11A11_mem_pres_iff.2 (by decide), by decide⟩, ?_⟩
  simp [s16c11A11c, Perm.sign_mul, Perm.sign_swap']

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
