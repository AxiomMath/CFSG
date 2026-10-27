module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalStd
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

public section

namespace CFSG.StandardType

namespace GGOppRad

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] [Finite K]

omit [Finite K] in
theorem transvection_apply_of_not {i j : ι} (hij : i ≠ j) (x : K) {c a : ι}
    (h : ¬ (c = i ∧ a = j)) :
    ((Matrix.SpecialLinearGroup.transvection hij x : Matrix.SpecialLinearGroup ι K) :
      Matrix ι ι K) c a = (1 : Matrix ι ι K) c a := by
  have h' : ¬ (i = c ∧ j = a) := fun h' => h ⟨h'.1.symm, h'.2.symm⟩
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.single_apply]
  simp [h']

theorem transvection_mem_stdU {ℓ : ι → ℕ} {i j : ι} (hij : i ≠ j) (h : ℓ i < ℓ j) (x : K) :
    Matrix.SpecialLinearGroup.transvection hij x ∈ stdU ℓ :=
  mem_stdU_iff.mpr fun _ _ hca => transvection_apply_of_not hij x fun ⟨hc, ha⟩ =>
    hca (hc ▸ ha ▸ h)

theorem transvection_mem_stdUop {ℓ : ι → ℕ} {i j : ι} (hij : i ≠ j) (h : ℓ j < ℓ i) (x : K) :
    Matrix.SpecialLinearGroup.transvection hij x ∈ stdUop ℓ :=
  mem_stdUop_iff.mpr fun _ _ hac => transvection_apply_of_not hij x fun ⟨hc, ha⟩ =>
    hac (hc ▸ ha ▸ h)

theorem sup_stdU_stdUop {ℓ : ι → ℕ} (h : ∃ c a, ℓ c < ℓ a) :
    stdU (K := K) ℓ ⊔ stdUop ℓ = ⊤ := by
  have hmem : ∀ {i j : ι} (hij : i ≠ j), ℓ i ≠ ℓ j → ∀ x : K,
      Matrix.SpecialLinearGroup.transvection hij x ∈ stdU (K := K) ℓ ⊔ stdUop ℓ := by
    intro i j hij hne x
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Subgroup.mem_sup_left (transvection_mem_stdU hij hlt x)
    · exact Subgroup.mem_sup_right (transvection_mem_stdUop hij hgt x)
  rw [eq_top_iff,
    ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
    Subgroup.closure_le]
  rintro _ ⟨⟨i, j, hij, x⟩, rfl⟩
  rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
  by_cases hne : ℓ i = ℓ j
  · obtain ⟨c, a, hca⟩ := h
    obtain ⟨d, hd⟩ : ∃ d, ℓ d ≠ ℓ i := by
      by_cases hc : ℓ c = ℓ i
      · exact ⟨a, by omega⟩
      · exact ⟨c, hc⟩
    have hid : i ≠ d := fun h' => hd (h' ▸ rfl)
    have hdj : d ≠ j := fun h' => hd (h' ▸ hne.symm)
    have hcomm := Matrix.SpecialLinearGroup.commutatorElement_transvection hid hdj hij x (1 : K)
    rw [mul_one] at hcomm
    rw [← hcomm, commutatorElement_def]
    have h1 := hmem hid (Ne.symm hd) x
    have h2 := hmem hdj (by omega) (1 : K)
    exact mul_mem (mul_mem (mul_mem h1 h2) (inv_mem h1)) (inv_mem h2)
  · exact hmem hij hne x

end GGOppRad

end CFSG.StandardType
