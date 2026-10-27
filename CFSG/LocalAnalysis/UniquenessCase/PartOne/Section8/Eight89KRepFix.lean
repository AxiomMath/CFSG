module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

private theorem k91fix_mul_sum {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (f : Module.End R W) (h5 : f ^ 5 = 1) :
    f * ∑ m ∈ Finset.range 5, f ^ m = ∑ m ∈ Finset.range 5, f ^ m := by
  have key : ∀ n : ℕ, f * ∑ m ∈ Finset.range n, f ^ m = ∑ m ∈ Finset.range n, f ^ (m + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, mul_add, ih, ← pow_succ', Finset.sum_range_succ]
  calc f * ∑ m ∈ Finset.range 5, f ^ m
      = ∑ m ∈ Finset.range 5, f ^ (m + 1) := key 5
    _ = ∑ m ∈ Finset.range 4, f ^ (m + 1) + f ^ 5 := Finset.sum_range_succ _ 4
    _ = ∑ m ∈ Finset.range 4, f ^ (m + 1) + f ^ 0 := by rw [h5, pow_zero]
    _ = ∑ m ∈ Finset.range 5, f ^ m := (Finset.sum_range_succ' (fun m => f ^ m) 4).symm

theorem exists_fixed_of_sum_pow_ne_zero {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (f : Module.End R W) (h5 : f ^ 5 = 1) (hP : ∑ m ∈ Finset.range 5, f ^ m ≠ 0) :
    ∃ w : W, w ≠ 0 ∧ f w = w := by
  obtain ⟨w₀, hw₀⟩ := DFunLike.ne_iff.mp hP
  refine ⟨(∑ m ∈ Finset.range 5, f ^ m) w₀, hw₀, ?_⟩
  rw [← Module.End.mul_apply, k91fix_mul_sum f h5]

private theorem k91tr3_fix_of_mem_zpowers {K R W : Type*} [Group K] [CommRing R] [AddCommGroup W]
    [Module R W] (ρ : K →* Module.End R W) {z z₀ : K} (hz : z ∈ Subgroup.zpowers z₀) {u : W}
    (hu : ρ z₀ u = u) : ρ z u = u := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  clear hz
  have hinv : ρ z₀⁻¹ u = u := by
    calc ρ z₀⁻¹ u = ρ z₀⁻¹ (ρ z₀ u) := by rw [hu]
      _ = u := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
  induction k with
  | zero => simp
  | succ i ih => rw [zpow_add_one, map_mul, Module.End.mul_apply, hu, ih]
  | pred i ih => rw [zpow_sub_one, map_mul, Module.End.mul_apply, hinv, ih]

private theorem k91tr3_apply_fix {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
    (g : Module.End R W) (hg3 : g ^ 3 = 1) (w : W) :
    g ((1 + g + g ^ 2 : Module.End R W) w) = (1 + g + g ^ 2 : Module.End R W) w := by
  have h3 : g (g (g w)) = w := by
    have := congrArg (fun T : Module.End R W => T w) hg3
    simpa [pow_succ, Module.End.mul_apply] using this
  simp only [LinearMap.add_apply, Module.End.one_apply, pow_two, Module.End.mul_apply, map_add, h3]
  exact (add_rotate _ _ _).symm

theorem one_add_add_sq_eq_zero {K R W : Type*} [Group K] [CommRing R] [AddCommGroup W]
    [Module R W] (ρ : K →* Module.End R W) {z z₀ : K} (hz₀ : z₀ ^ 3 = 1)
    (hz : z ∈ Subgroup.zpowers z₀) (hfix : ∀ w : W, ρ z w = w → w = 0) :
    1 + ρ z₀ + ρ z₀ ^ 2 = 0 := by
  have hg3 : ρ z₀ ^ 3 = 1 := by rw [← map_pow, hz₀, map_one]
  exact LinearMap.ext fun w =>
    hfix _ (k91tr3_fix_of_mem_zpowers ρ hz (k91tr3_apply_fix _ hg3 w))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs
