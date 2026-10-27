module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG

namespace FiveTransitive.InvariantSylow

open MulAction
open scoped Pointwise

private theorem exists_invariant
    (p : ℕ) [Fact p.Prime]
    (A H : Type*) [Group A] [Group H] [Finite H]
    [MulDistribMulAction A H] (hA : IsPGroup p A) :
    ∃ P : Sylow p H, ∀ a : A, ∀ h : H, h ∈ P → a • h ∈ P := by
  classical
  let P₀ : Sylow p H := Classical.choice inferInstance
  have hnot : ¬ p ∣ Nat.card (Sylow p H) := by
    intro h
    exact P₀.not_dvd_index (h.trans P₀.card_dvd_index)
  obtain ⟨P, hP⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p H) hnot
  refine ⟨P, ?_⟩
  intro a h hh
  have heq : a • (P : Subgroup H) = P := by
    rw [← Sylow.pointwise_smul_def, (mem_fixedPoints.mp hP) a]
  change a • h ∈ (P : Subgroup H)
  rw [← heq]
  exact Subgroup.smul_mem_pointwise_smul h a (P : Subgroup H) hh

theorem exists_invariant_hom
    (p : ℕ) [Fact p.Prime]
    (A H : Type*) [Group A] [Group H] [Finite H]
    (hA : IsPGroup p A) (f : A →* MulAut H) :
    ∃ P : Sylow p H, ∀ a : A, ∀ h : H, h ∈ P → f a h ∈ P := by
  let _ : MulDistribMulAction A H := MulDistribMulAction.compHom H f
  exact exists_invariant p A H hA

end FiveTransitive.InvariantSylow

end CFSG
