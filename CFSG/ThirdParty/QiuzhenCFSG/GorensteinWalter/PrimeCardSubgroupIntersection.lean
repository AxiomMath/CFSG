module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Intersections with prime-cardinality subgroups

A proper intersection with a subgroup of prime cardinality is trivial.  This
packages the repeated subgroup-of-subgroup argument without choosing a
generator.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- If a prime-cardinality subgroup `P` is not contained in `H`, then
`H ∩ P` is trivial. -/
public theorem inf_eq_bot_of_not_le_of_prime_card
    {G : Type u} [Group G] [Finite G]
    (H P : Subgroup G)
    (hp : (Nat.card P).Prime)
    (hnot : ¬ P ≤ H) :
    H ⊓ P = ⊥ := by
  classical
  let I : Subgroup P := (H ⊓ P).subgroupOf P
  let : Fact (Nat.card P).Prime := ⟨hp⟩
  rcases I.eq_bot_or_eq_top_of_prime_card with hbot | htop
  · apply le_antisymm
    · intro x hx
      let xP : P := ⟨x, hx.2⟩
      have hxI : xP ∈ I := Subgroup.mem_subgroupOf.mpr hx
      have hxbot : xP ∈ (⊥ : Subgroup P) := by simpa [hbot] using hxI
      exact Subgroup.mem_bot.mpr
        (congrArg Subtype.val (Subgroup.mem_bot.mp hxbot))
    · exact bot_le
  · exfalso
    apply hnot
    intro x hxP
    let xP : P := ⟨x, hxP⟩
    have hxI : xP ∈ I := by rw [htop]; trivial
    exact (Subgroup.mem_subgroupOf.mp hxI).1

end CFSG.GorensteinWalter
