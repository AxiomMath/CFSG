module

public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

namespace CFSG.GorensteinWalter

universe u

/-- A nontrivial abelian subgroup is not its own commutator. -/
public theorem commutator_ne_self_of_abelian_nontrivial
    {G : Type u} [Group G] (B : Subgroup G)
    (hB : IsMulCommutative B) (hBne : B ≠ ⊥) :
    ⁅B, B⁆ ≠ B := by
  intro heq
  have hbot : ⁅B, B⁆ = ⊥ :=
    (Subgroup.commutator_self_eq_bot_iff).mpr hB
  have hBbot : B = ⊥ := by
    rw [← heq]
    exact hbot
  exact hBne hBbot

end CFSG.GorensteinWalter
