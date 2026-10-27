module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

public section

namespace CFSG

namespace FiveTransitive.PatternFixerNormalizer

open MulAction Equiv

theorem normalizes_range
    {G X I : Type*} [Group G] [MulAction G X]
    (a : G) (e : I ↪ X) (π : Perm I) (he : ∀ i, a • e i = e (π i)) :
    a ∈ Subgroup.normalizer (fixingSubgroup G (Set.range e) : Set G) := by
  have hforward : ∀ x ∈ Set.range e, a • x ∈ Set.range e := by
    rintro _ ⟨i,rfl⟩
    exact ⟨π i,(he i).symm⟩
  have hback : ∀ x ∈ Set.range e, a⁻¹ • x ∈ Set.range e := by
    rintro _ ⟨i,rfl⟩
    refine ⟨π.symm i,?_⟩
    symm
    apply (inv_smul_eq_iff).mpr
    simpa using (he (π.symm i)).symm
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    rw [mem_fixingSubgroup_iff] at hu ⊢
    intro x hx
    rw [mul_smul,mul_smul,hu _ (hback x hx),smul_inv_smul]
  · intro hu
    rw [mem_fixingSubgroup_iff] at hu ⊢
    intro x hx
    have h := hu (a • x) (hforward x hx)
    simpa only [mul_smul,inv_smul_smul,smul_left_cancel_iff] using h

end FiveTransitive.PatternFixerNormalizer

end CFSG
