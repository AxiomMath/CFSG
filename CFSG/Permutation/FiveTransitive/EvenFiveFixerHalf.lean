module

public import CFSG.Permutation.FiveTransitive.SignKernelTransitivity
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG

namespace FiveTransitive.EvenFiveFixerHalf

open MulAction

theorem five_transitive
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (h5 : IsMultiplyPretransitive P X 5)
    (hodd : ∀ s : Set X, s.ncard = 5 →
      ∃ g : fixingSubgroup P s, Equiv.Perm.sign g.val.val = -1) :
    IsMultiplyPretransitive (P ⊓ alternatingGroup X : Subgroup (Equiv.Perm X)) X 5 := by
  rw [isMultiplyPretransitive_iff]
  intro a b
  obtain ⟨g,hg⟩ := h5.exists_smul_eq a b
  rcases Int.units_eq_one_or (Equiv.Perm.sign g.val) with heven | hgodd
  · refine ⟨⟨g.val,g.property,Equiv.Perm.mem_alternatingGroup.mpr heven⟩,?_⟩
    ext i
    exact DFunLike.congr_fun hg i
  · have ha : (Set.range a).ncard = 5 := by
      simpa only [Nat.card_fin] using Set.ncard_range_of_injective a.injective
    obtain ⟨z,hz⟩ := hodd (Set.range a) ha
    refine ⟨⟨g.val * z.val.val,P.mul_mem g.property z.val.property,?_⟩,?_⟩
    · change Equiv.Perm.sign (g.val * z.val.val) = 1
      rw [map_mul,hgodd,hz]
      norm_num
    · ext i
      change (g * z.val) • a i = b i
      rw [mul_smul,(mem_fixingSubgroup_iff P).mp z.property (a i) ⟨i,rfl⟩]
      exact DFunLike.congr_fun hg i

end FiveTransitive.EvenFiveFixerHalf

end CFSG
