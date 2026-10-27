module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Existence of a reflection in the fixed dihedral Sylow subgroup
-/

namespace CFSG.GorensteinWalter

universe u

/-- The cyclic subgroup `S0` has index two in `S`, so `S \ S0` is
nonempty. -/
public theorem CentralizerSetup.exists_reflection
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) :
    ∃ r : G, c.IsReflection r := by
  have hne : c.S0 ≠ (c.S : Subgroup G) := by
    intro heq
    have hcardS0 : Nat.card c.S0 = Nat.card c.S := by rw [heq]
    have hcard : Nat.card (c.S : Subgroup G) = 2 * Nat.card c.S0 :=
      c.S_index_two
    rw [hcardS0] at hcard
    have hpos : 0 < Nat.card c.S0 := Nat.card_pos
    omega
  have hnotle : ¬ (c.S : Subgroup G) ≤ c.S0 := by
    intro hle
    exact hne (le_antisymm c.S0_le_S hle)
  rcases Set.not_subset.mp hnotle with ⟨r, hrS, hrnot⟩
  exact ⟨r, hrS, hrnot⟩

end CFSG.GorensteinWalter
