module

public import CFSG.Permutation.FiveTransitive.Degree80TwoBound

public section

namespace CFSG

namespace FiveTransitive.Degree80FactorizationBounds
open MulAction SylowFixedActionCore

theorem two_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    (Nat.card (fixingSubgroup P s)).factorization 2 ≤ 36 := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  let S : Sylow 2 (fixingSubgroup P s) := Sylow.nonempty.some
  have hb := Degree80TwoBound.sylow_card_le P hcard h5 hnotAlt s hs S
  rw [S.card_eq_multiplicity] at hb
  by_contra hn
  have hh := Nat.pow_le_pow_right (by decide : 0 < 2)
    (by omega : 37 ≤ (Nat.card (fixingSubgroup P s)).factorization 2)
  norm_num only [Nat.reducePow] at hh
  omega

end FiveTransitive.Degree80FactorizationBounds

end CFSG
