module

public import CFSG.Permutation.FiveTransitive.Degree39ThreeBound

public section

namespace CFSG

namespace FiveTransitive.Degree39TwoPartBound

open MulAction

private theorem card_dvd_exterior_tuples
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 39)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ∣ (34 : ℕ).descFactorial 15 := by
  have hfix : 5 ≤ Nat.card (fixedPoints (fixingSubgroup P s) X) := by
    rw [Nat.card_coe_set_eq,← hs]
    exact Set.ncard_le_ncard (by
      intro x hx q
      exact (mem_fixingSubgroup_iff P).mp q.property x hx)
  exact Degree39ThreeBound.card_dvd_exterior_tuples P hcard h5 hnotAlt
    (fixingSubgroup P s) 5 15 (by norm_num) hfix

theorem two_pow_dvd_bound
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 39)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (a : ℕ)
    (ha : 2 ^ a ∣ Nat.card (fixingSubgroup P s)) : a ≤ 16 := by
  by_contra hn
  have hd : 2 ^ 17 ∣ Nat.card (fixingSubgroup P s) :=
    (pow_dvd_pow 2 (by omega : 17 ≤ a)).trans ha
  have hc := hd.trans (card_dvd_exterior_tuples P hcard h5 hnotAlt s hs)
  norm_num [Nat.descFactorial] at hc

end FiveTransitive.Degree39TwoPartBound

end CFSG
