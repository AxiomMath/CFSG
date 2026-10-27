module

public import CFSG.Permutation.FiveTransitive.Degree80FiveOrder

public section

namespace CFSG

namespace FiveTransitive.Degree80OddFactorizationBounds
open MulAction

theorem three_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    (Nat.card (fixingSubgroup P s)).factorization 3 ≤ 1 := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let S : Sylow 3 (fixingSubgroup P s) := Sylow.nonempty.some
  have hb := Degree80ThreeCyclic.sylow_card_le_three P hcard h5 hnotAlt s hs S
  rw [S.card_eq_multiplicity] at hb
  by_contra hn
  have hh := Nat.pow_le_pow_right (by decide : 0 < 3)
    (by omega : 2 ≤ (Nat.card (fixingSubgroup P s)).factorization 3)
  norm_num only [Nat.reducePow] at hh
  omega

theorem five_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    (Nat.card (fixingSubgroup P s)).factorization 5 ≤ 2 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let S : Sylow 5 (fixingSubgroup P s) := Sylow.nonempty.some
  have hb := Degree80FiveOrder.sylow_card_le_twenty_five P hcard h5 hnotAlt s hs S
  rw [S.card_eq_multiplicity] at hb
  by_contra hn
  have hh := Nat.pow_le_pow_right (by decide : 0 < 5)
    (by omega : 3 ≤ (Nat.card (fixingSubgroup P s)).factorization 5)
  norm_num only [Nat.reducePow] at hh
  omega

end FiveTransitive.Degree80OddFactorizationBounds

end CFSG
