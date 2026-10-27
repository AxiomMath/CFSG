module

public import CFSG.Permutation.FiveTransitive.Degree54FiveGroupBound

public section

namespace CFSG

namespace FiveTransitive.Degree54FiveFixerBounds
open MulAction

theorem two_pow_dvd_bound
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (a : ℕ)
    (ha : 2 ^ a ∣ Nat.card (fixingSubgroup P s)) : a ≤ 23 := by
  have hfix : 5 ≤ Nat.card (fixedPoints (fixingSubgroup P s) X) := by
    rw [Nat.card_coe_set_eq,← hs]
    exact Set.ncard_le_ncard (by
      intro x hx q
      exact (mem_fixingSubgroup_iff P).mp q.property x hx)
  have hd := Degree54FiveGroupBound.card_dvd_exterior_tuples
    P hcard h5 hnotAlt (fixingSubgroup P s) 5 23 (by norm_num) hfix
  by_contra hn
  have hb : 2 ^ 24 ∣ Nat.card (fixingSubgroup P s) :=
    (pow_dvd_pow 2 (by omega : 24 ≤ a)).trans ha
  have hc := hb.trans hd
  norm_num [Nat.descFactorial] at hc

theorem three_pow_dvd_bound
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (a : ℕ)
    (ha : 3 ^ a ∣ Nat.card (fixingSubgroup P s)) : a ≤ 12 := by
  have hfix : 5 ≤ Nat.card (fixedPoints (fixingSubgroup P s) X) := by
    rw [Nat.card_coe_set_eq,← hs]
    exact Set.ncard_le_ncard (by
      intro x hx q
      exact (mem_fixingSubgroup_iff P).mp q.property x hx)
  have hd := Degree54FiveGroupBound.card_dvd_exterior_tuples
    P hcard h5 hnotAlt (fixingSubgroup P s) 5 23 (by norm_num) hfix
  by_contra hn
  have hb : 3 ^ 13 ∣ Nat.card (fixingSubgroup P s) :=
    (pow_dvd_pow 3 (by omega : 13 ≤ a)).trans ha
  have hc := hb.trans hd
  norm_num [Nat.descFactorial] at hc

end FiveTransitive.Degree54FiveFixerBounds

end CFSG
