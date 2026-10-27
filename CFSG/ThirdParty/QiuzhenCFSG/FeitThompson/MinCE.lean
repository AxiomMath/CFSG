module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finite.Defs
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Solvable
import Mathlib.Tactic.TypeStar

namespace CFSG
end CFSG
open CFSG

open scoped commutatorElement
open scoped IsMulCommutative

/-- Minimal counter-example. -/
public class CFSG.IsMinCE (G : Type*) [Group G] [Finite G] : Prop where
  odd_order : Odd (Nat.card G)
  -- We require simpleness here.
  simple : IsSimpleGroup G
  not_solvable : ¬ Group.IsSolvable G
  proper_subgroups_solvable : ∀ (H : Subgroup G), H < ⊤ → Group.IsSolvable H

/-- `G` is not abelian. -/
theorem CFSG.not_comm_of_min_ce {G : Type*} [Group G] [Finite G]
    [IsMinCE G] : ¬ IsMulCommutative G := by
  intro hcomm
  have hSol : Group.IsSolvable G := by
    refine ⟨1, ?_⟩
    have h1 : commutatorSet G ⊆ {(1 : G)} := by
      intro x hx
      rcases mem_commutatorSet_iff.mp hx with ⟨g₁, g₂, rfl⟩
      calc
        ⁅g₁, g₂⁆
        _ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ := rfl
        _ = 1 := by simp only [mul_inv_cancel_comm, mul_inv_cancel]
    have hle : commutator G ≤ ⊥ := by
      calc
        commutator G = Subgroup.closure (commutatorSet G) := by rw [commutator_eq_closure]
        _ ≤ Subgroup.closure {(1 : G)} := Subgroup.closure_mono h1
        _ = ⊥ := by simp only [Subgroup.closure_eq_bot_iff, subset_refl]
    exact le_antisymm hle (OrderBot.bot_le (commutator G))
  have : ¬ Group.IsSolvable G := IsMinCE.not_solvable
  exact this hSol

/-- The center of `G` is trivial. -/
public theorem CFSG.center_eq_bot_of_min_ce {G : Type*} [Group G] [Finite G]
    [IsMinCE G] : Subgroup.center G = ⊥ := by
  have : IsSimpleGroup G := IsMinCE.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hc | hc
  · exact hc
  · exfalso
    have hcomm : IsMulCommutative G := by
      refine { is_comm := ⟨fun a b => ?_⟩ }
      have ha : a ∈ Subgroup.center G := by rw [hc]; exact Subgroup.mem_top a
      have hb : b ∈ Subgroup.center G := by rw [hc]; exact Subgroup.mem_top b
      rw [Subgroup.mem_center_iff] at ha hb
      exact (ha b).symm
    exact not_comm_of_min_ce hcomm

/-- A finite `p`-subgroup of a minimal counterexample is a proper subgroup. -/
public theorem CFSG.IsMinCE.pSubgroup_ne_top {G : Type*} [Group G] [Finite G] [IsMinCE G]
    {P : Subgroup G} {p : ℕ} [Fact p.Prime] (hPp : IsPGroup p P) :
    P ≠ ⊤ := by
  intro hPtop
  have htop_p : IsPGroup p (⊤ : Subgroup G) :=
    hPp.of_equiv (MulEquiv.subgroupCongr hPtop)
  have hGp : IsPGroup p G :=
    htop_p.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
  have hnilpotent : Group.IsNilpotent G :=
    IsPGroup.isNilpotent (p := p) (G := G) (h := hGp)
  have hsolvable : Group.IsSolvable G := @IsNilpotent.to_isSolvable G _ hnilpotent
  exact IsMinCE.not_solvable (G := G) hsolvable
