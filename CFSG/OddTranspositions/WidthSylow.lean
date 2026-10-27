module

public import CFSG.Timmesfeld.Bridge.OddTranspBasic

public section

namespace CFSG.OddTranspositions

open scoped Pointwise

variable {X : Type} [Group X] {E : Set X}

theorem center_le_solvableRadical (G : Type) [Group G] [Finite G] :
    Subgroup.center G ≤ CFSG.solvableRadical G := by
  haveI : Group.IsSolvable (Subgroup.center G) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)
  exact CFSG.Timmesfeld.Bridge.OddTransp.le_solvableRadical (N := Subgroup.center G)
    inferInstance inferInstance

theorem center_eq_bot_of_solvableRadical_eq_bot {G : Type} [Group G] [Finite G]
    (h : CFSG.solvableRadical G = ⊥) : Subgroup.center G = ⊥ := by
  apply le_antisymm
  · calc Subgroup.center G ≤ CFSG.solvableRadical G := center_le_solvableRadical G
      _ = ⊥ := h
  · exact bot_le

theorem normal_isPGroup_le_solvableRadical {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {N : Subgroup G} (hN : N.Normal) (hP : IsPGroup p N) :
    N ≤ CFSG.solvableRadical G := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsNilpotent N := hP.isNilpotent
  exact CFSG.Timmesfeld.Bridge.OddTransp.le_solvableRadical hN inferInstance

theorem eq_bot_of_normal_isPGroup_of_solvableRadical_eq_bot {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {N : Subgroup G} (hN : N.Normal) (hP : IsPGroup p N)
    (h : CFSG.solvableRadical G = ⊥) : N = ⊥ := by
  apply le_antisymm
  · calc N ≤ CFSG.solvableRadical G := normal_isPGroup_le_solvableRadical hp hN hP
      _ = ⊥ := h
  · exact bot_le

end CFSG.OddTranspositions

