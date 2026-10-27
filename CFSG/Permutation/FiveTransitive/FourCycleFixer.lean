module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG

namespace FiveTransitive.FourCycleFixer

open MulAction

theorem exists_four_set
    (G X : Type*) [Group G] [MulAction G X]
    (a : G) (ha4 : a ^ 4 = 1) (x : X) (hx : a ^ 2 • x ≠ x) :
    ∃ s : Set X, s.ncard = 4 ∧ x ∈ s ∧
      a ∈ Subgroup.normalizer (fixingSubgroup G s : Set G) := by
  classical
  let f := MulAction.toPermHom G X a
  have hf4 : f (f (f (f x))) = x := by
    change a • (a • (a • (a • x))) = x
    simpa only [pow_succ, pow_zero, mul_smul, one_smul] using
      (show a ^ 4 • x = x by rw [ha4, one_smul])
  have h02 : x ≠ f (f x) := by
    intro h
    apply hx
    simpa [f, pow_two, mul_smul] using h.symm
  have h01 : x ≠ f x := by
    intro h
    apply h02
    exact h.trans (congrArg f h)
  have h12 : f x ≠ f (f x) := fun h => h01 (f.injective h)
  have h23 : f (f x) ≠ f (f (f x)) := fun h => h12 (f.injective h)
  have h13 : f x ≠ f (f (f x)) := fun h => h02 (f.injective h)
  have h03 : x ≠ f (f (f x)) := by
    intro h
    have h' := congrArg f h
    rw [hf4] at h'
    exact h01 h'.symm
  let e : Fin 4 ↪ X := ⟨![x, f x, f (f x), f (f (f x))], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  let s : Set X := Set.range e
  have hs : s.ncard = 4 := by
    simpa only [s, Nat.card_fin] using Set.ncard_range_of_injective e.injective
  have hax : ∀ y ∈ s, a • y ∈ s := by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · refine ⟨0, ?_⟩
      exact hf4.symm
  have haxinv : ∀ y ∈ s, a⁻¹ • y ∈ s := by
    have hainv : a⁻¹ = a ^ 3 := by
      symm
      apply eq_inv_iff_mul_eq_one.mpr
      simpa only [← pow_succ] using ha4
    intro y hy
    rw [hainv]
    simpa only [pow_succ, pow_zero, mul_smul, one_smul] using
      hax (a • (a • y)) (hax (a • y) (hax y hy))
  refine ⟨s, hs, ⟨0, rfl⟩, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    rw [mem_fixingSubgroup_iff] at hu ⊢
    intro y hy
    rw [mul_smul, mul_smul, hu _ (haxinv y hy), smul_inv_smul]
  · intro hu
    rw [mem_fixingSubgroup_iff] at hu ⊢
    intro y hy
    have h := hu (a • y) (hax y hy)
    simpa only [mul_smul, inv_smul_smul, smul_left_cancel_iff] using h

end FiveTransitive.FourCycleFixer

end CFSG
