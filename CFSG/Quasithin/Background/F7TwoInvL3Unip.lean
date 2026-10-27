module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LinearAlgebra.LinearGroups.Generation
public import CFSG.Quasithin.Background.F7TwoInvAutWrap

public section

namespace CFSG.Quasithin.F7Two

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LinearGroups
open scoped MatrixGroups

section Lower

variable (n : ℕ) (K : Type*) [Field K]

@[expose] def lowerUnitriangular : Subgroup (SpecialLinearGroup (Fin n) K) where
  carrier := {A | SpecialLinearGroup.transpose A ∈ unitriangular n K}
  one_mem' := by
    have h : SpecialLinearGroup.transpose (1 : SpecialLinearGroup (Fin n) K) = 1 :=
      Subtype.ext (by simp [SpecialLinearGroup.coe_transpose])
    show SpecialLinearGroup.transpose (1 : SpecialLinearGroup (Fin n) K) ∈ unitriangular n K
    rw [h]
    exact one_mem _
  mul_mem' := by
    intro A B hA hB
    have h : SpecialLinearGroup.transpose (A * B) =
        SpecialLinearGroup.transpose B * SpecialLinearGroup.transpose A :=
      Subtype.ext (by simp [Matrix.transpose_mul])
    show SpecialLinearGroup.transpose (A * B) ∈ unitriangular n K
    rw [h]
    exact mul_mem hB hA
  inv_mem' := by
    intro A hA
    have h : SpecialLinearGroup.transpose A⁻¹ = (SpecialLinearGroup.transpose A)⁻¹ :=
      Subtype.ext (by simp [Matrix.adjugate_transpose])
    show SpecialLinearGroup.transpose A⁻¹ ∈ unitriangular n K
    rw [h]
    exact inv_mem hA

variable {n K}

theorem mem_lowerUnitriangular {A : SpecialLinearGroup (Fin n) K} :
    A ∈ lowerUnitriangular n K ↔
      (∀ i j : Fin n, i < j → (A : Matrix (Fin n) (Fin n) K) i j = 0) ∧
        ∀ i : Fin n, (A : Matrix (Fin n) (Fin n) K) i i = 1 := by
  show SpecialLinearGroup.transpose A ∈ unitriangular n K ↔ _
  rw [mem_unitriangular]
  simp only [SpecialLinearGroup.coe_transpose, Matrix.transpose_apply]
  exact ⟨fun ⟨h1, h2⟩ => ⟨fun i j hij => h1 j i hij, h2⟩,
    fun ⟨h1, h2⟩ => ⟨fun i j hij => h1 j i hij, h2⟩⟩

theorem unitriangular_sup_lowerUnitriangular :
    unitriangular n K ⊔ lowerUnitriangular n K = ⊤ := by
  rw [eq_top_iff, ← special_linear_elementary_generation (K := K) (n := n), Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  have hc : ((SpecialLinearGroup.transvection hij c : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 + single i j c := rfl
  rcases lt_or_gt_of_ne hij with h | h
  · refine Subgroup.mem_sup_left (mem_unitriangular.mpr ⟨fun a b hba => ?_, fun a => ?_⟩)
    · rw [hc]
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
      have hab : a ≠ b := ne_of_gt hba
      have hne : ¬ (i = a ∧ j = b) := fun ⟨h1, h2⟩ => by
        subst h1; subst h2; exact absurd (lt_trans hba h) (lt_irrefl _)
      simp [hab, hne]
    · rw [hc]
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
      have hne : ¬ (i = a ∧ j = a) := fun ⟨h1, h2⟩ => hij (h1.trans h2.symm)
      simp [hne]
  · refine Subgroup.mem_sup_right (mem_lowerUnitriangular.mpr ⟨fun a b hab => ?_, fun a => ?_⟩)
    · rw [hc]
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
      have hab' : a ≠ b := ne_of_lt hab
      have hne : ¬ (i = a ∧ j = b) := fun ⟨h1, h2⟩ => by
        subst h1; subst h2; exact absurd (lt_trans hab h) (lt_irrefl _)
      simp [hab', hne]
    · rw [hc]
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
      have hne : ¬ (i = a ∧ j = a) := fun ⟨h1, h2⟩ => hij (h1.trans h2.symm)
      simp [hne]

theorem natCard_lowerUnitriangular :
    Nat.card (lowerUnitriangular n K) = Nat.card (unitriangular n K) :=
  Nat.card_congr
    { toFun := fun A => ⟨SpecialLinearGroup.transpose A.1, A.2⟩
      invFun := fun B => ⟨SpecialLinearGroup.transpose B.1, by
        show SpecialLinearGroup.transpose (SpecialLinearGroup.transpose B.1) ∈ unitriangular n K
        have h : SpecialLinearGroup.transpose (SpecialLinearGroup.transpose B.1) = B.1 :=
          Subtype.ext (by simp [SpecialLinearGroup.coe_transpose])
        rw [h]
        exact B.2⟩
      left_inv := fun A => Subtype.ext (Subtype.ext (by simp [SpecialLinearGroup.coe_transpose]))
      right_inv := fun B => Subtype.ext (Subtype.ext (by simp [SpecialLinearGroup.coe_transpose])) }

end Lower

section Criterion

variable {K : Type*} [Field K] [Finite K]

theorem odd_natCard_unitriangular_three (hodd : Odd (Nat.card K)) :
    Odd (Nat.card (unitriangular 3 K)) := by
  rw [card_unitriangular]
  exact hodd.pow

theorem odd_natCard_lowerUnitriangular_three (hodd : Odd (Nat.card K)) :
    Odd (Nat.card (lowerUnitriangular 3 K)) := by
  rw [natCard_lowerUnitriangular]
  exact odd_natCard_unitriangular_three hodd

theorem invAutGen_of_unitriangular_invariant (hodd : Odd (Nat.card K)) {X : Type*} [Group X]
    [Finite X] (hs : IsSimpleGroup X) (hnonab : ∃ x y : X, x * y ≠ y * x)
    (θ : SpecialLinearGroup (Fin 3) K →* X) (hθ : Function.Surjective θ) {φ : MulAut X}
    (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1)
    (α : SpecialLinearGroup (Fin 3) K → SpecialLinearGroup (Fin 3) K)
    (hα : ∀ x, φ (θ x) = θ (α x)) (hU : ∀ u ∈ unitriangular 3 K, α u ∈ unitriangular 3 K)
    (hL : ∀ u ∈ lowerUnitriangular 3 K, α u ∈ lowerUnitriangular 3 K) : InvAutGen X φ := by
  refine invAutGen_of_odd_sup hs hnonab hφ2 hφ1
    (U₁ := (unitriangular 3 K).map θ) (U₂ := (lowerUnitriangular 3 K).map θ) ?_ ?_ ?_ ?_ ?_
  · exact (odd_natCard_unitriangular_three hodd).of_dvd_nat (Subgroup.card_map_dvd _ _)
  · exact (odd_natCard_lowerUnitriangular_three hodd).of_dvd_nat (Subgroup.card_map_dvd _ _)
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨α u, hU u hu, (hα u).symm⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact ⟨α u, hL u hu, (hα u).symm⟩
  · rw [← Subgroup.map_sup, unitriangular_sup_lowerUnitriangular,
      Subgroup.map_top_of_surjective _ hθ]

end Criterion

end CFSG.Quasithin.F7Two
