module

public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport

public section

namespace CFSG

namespace FiveTransitive.MinimalOrbitFixedBounds

open MulAction

theorem fixed_card_le_half
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : 28 ≤ Fintype.card X)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : Q ≠ ⊥) :
    Nat.card (fixedPoints Q X) ≤ Fintype.card X / 2 := by
  let _ : Nontrivial Q := Q.nontrivial_iff_ne_bot.mpr hQ
  obtain ⟨q,hq⟩ := exists_ne (1 : Q)
  have hne : q.val.val ≠ 1 := fun h => hq (Subtype.ext (Subtype.ext h))
  have hm := HighDegreeManningSupport.degree_le_two_mul_support P hcard h5 hnotAlt q.val.property hne
  have hsub : fixedPoints Q X ⊆ (q.val.val.support : Set X)ᶜ := by
    intro y hy
    change ¬ y ∈ q.val.val.support
    rw [Equiv.Perm.mem_support,not_not]
    have hh := hy q
    change q.val.val y = y at hh
    exact hh
  have hl := Set.ncard_le_ncard hsub
  rw [←Nat.card_coe_set_eq,Set.ncard_compl,Set.ncard_coe_finset] at hl
  rw [show Nat.card X = Fintype.card X from Nat.card_eq_fintype_card] at hl
  omega

end FiveTransitive.MinimalOrbitFixedBounds

end CFSG
