module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KModel
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KRepFix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

private theorem k91m2f_two_eq_zero {W : Type} [AddCommGroup W] [Module (ZMod 2) W] :
    (2 : Module.End (ZMod 2) W) = 0 := by
  have h : (2 : Module.End (ZMod 2) W) = 1 + 1 := one_add_one_eq_two.symm
  refine h.trans (LinearMap.ext fun w => ?_)
  have hw : w + w = 0 := by
    rw [← two_smul (ZMod 2) w, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  simpa using hw

private theorem k91m2f_sum_eq_one {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    {x : Module.End (ZMod 2) W} (h : 1 + x + x ^ 2 = 0) : x + x ^ 2 = 1 := by
  have h2 : (1 : Module.End (ZMod 2) W) + 1 = 0 :=
    one_add_one_eq_two.trans k91m2f_two_eq_zero
  have h1 : (1 : Module.End (ZMod 2) W) + (x + x ^ 2) = 0 := by rwa [← add_assoc]
  rw [eq_neg_of_add_eq_zero_right h1, neg_eq_of_add_eq_zero_right h2]

theorem exists_fixed_model3_of_mod2 (hC : IdentC) (he3 : e3 ^ 5 = 1) {W : Type} [AddCommGroup W]
    [Module (ZMod 2) W] [Nontrivial W] (ρ : model3 →* Module.End (ZMod 2) W)
    (h : 1 + ρ c3 + ρ c3 ^ 2 = 0) : ∃ w : W, w ≠ 0 ∧ ρ e3 w = w := by
  obtain ⟨T, hT⟩ := hC
  have hP : ∑ m ∈ Finset.range 5, ρ e3 ^ m ≠ 0 := by
    intro hP0
    have key := hT (Module.End (ZMod 2) W) k91m2f_two_eq_zero ρ
    simp only [hP0, mul_zero, zero_mul, List.map_const', List.sum_replicate, smul_zero] at key
    rw [k91m2f_sum_eq_one h] at key
    exact one_ne_zero key.symm
  exact exists_fixed_of_sum_pow_ne_zero (ρ e3) (by rw [← map_pow, he3, map_one]) hP

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs
