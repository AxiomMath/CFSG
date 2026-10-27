module

public import CFSG.GroupTheory.PStableAction
public import CFSG.LocalAnalysis.SteinbergBQSolvableActionPStability
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.StronglyEmbedded

open CFSG.GroupTheory

theorem odd_order_stable_actions {p : ℕ} (hp : p.Prime) (hodd : Odd p) {G : Type*} [Group G]
    [Finite G] (hG : Odd (Nat.card G)) {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P)
    (ρ : G →* MulAut P) : IsPStableAction p ρ := by
  have : Group.IsSolvable G := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hG
  intro x hx
  have hx' : ∀ u : P, ρ x⁻¹ (u⁻¹ * ρ x⁻¹ u) = u⁻¹ * ρ x⁻¹ u := fun u =>
    (double_commutator_eq_one_iff ρ u x).1 (hx u)
  have h := CFSG.LocalAnalysis.SteinbergBQ.solvable_action_p_stability hp hodd hP ρ (Or.inr hG)
    (x := x⁻¹) hx'
  rw [actionPCore, Subgroup.mem_comap, QuotientGroup.mk'_apply, ← inv_inv x]
  exact inv_mem h

end CFSG.StronglyEmbedded
