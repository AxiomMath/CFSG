module

public import CFSG.Permutation.FiveTransitive.Degree28SylowThreeEntrance
public import CFSG.Permutation.FiveTransitive.Degree28SylowThreeClosure

public section

namespace CFSG

namespace FiveTransitive.Degree28ThreeFreeReduction

open MulAction

private theorem sylow_card_eq_one
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s)) : Nat.card S = 1 := by
  by_contra hS
  have h3 := Degree28SylowThreeEntrance.card_eq_three P hcard h5 hnotAlt s hs S hS
  exact hnotAlt (Degree28SylowThreeClosure.alternatingGroup_le P hcard h5 s hs S h3)

theorem three_not_dvd_five_fixer_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 3 ∣ Nat.card (fixingSubgroup P s) := by
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let S : Sylow 3 (fixingSubgroup P s) := Sylow.nonempty.some
  have hS := sylow_card_eq_one P hcard h5 hnotAlt s hs S
  have he := (S : Subgroup (fixingSubgroup P s)).index_mul_card
  rw [hS,mul_one] at he
  rw [← he]
  exact S.not_dvd_index

end FiveTransitive.Degree28ThreeFreeReduction

end CFSG
