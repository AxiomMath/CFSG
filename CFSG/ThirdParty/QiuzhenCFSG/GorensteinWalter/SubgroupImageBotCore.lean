module

public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- If a subgroup maps to the bottom of a quotient by a normal subgroup and
its intersection with that normal subgroup is trivial, then it is trivial. -/
public theorem subgroup_eq_bot_of_image_eq_bot
    {G : Type u} [Group G]
    (O P : Subgroup G) [O.Normal]
    (hinter : P ⊓ O = ⊥)
    (hmap : P.map (QuotientGroup.mk' O) = ⊥) :
    P = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hxmap : QuotientGroup.mk' O x ∈ P.map (QuotientGroup.mk' O) :=
    Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  rw [hmap] at hxmap
  have hxO : x ∈ O :=
    (QuotientGroup.eq_one_iff (N := O) x).mp (Subgroup.mem_bot.mp hxmap)
  have hxinf : x ∈ P ⊓ O := ⟨hx, hxO⟩
  have hxbot : x ∈ (⊥ : Subgroup G) := by
    rwa [hinter] at hxinf
  exact Subgroup.mem_bot.mp hxbot

end CFSG.GorensteinWalter
