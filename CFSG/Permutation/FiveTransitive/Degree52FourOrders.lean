module

public import CFSG.Permutation.FiveTransitive.Degree52TwoOrder

public section

namespace CFSG

namespace FiveTransitive.Degree52FourOrders

open MulAction

theorem five_fixer_card_cases
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) = 16 ∨ Nat.card (fixingSubgroup P s) = 32 ∨
      Nat.card (fixingSubgroup P s) = 48 ∨ Nat.card (fixingSubgroup P s) = 96 := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨a,b,_,_,hb,hH,_⟩ :=
    Degree52FiveFixerFactorization.card_exponents P hcard h5 hnotAlt s hs
  let S : Sylow 2 (fixingSubgroup P s) := Sylow.nonempty.some
  have hS := Degree52TwoOrder.card_sixteen_or_thirtyTwo P hcard h5 hnotAlt s hs S
  have hdiv : 2 ^ a ∣ Nat.card S :=
    S.pow_dvd_card_of_pow_dvd_card (n := a) (by rw [hH]; exact dvd_mul_right _ _)
  have hle : 2 ^ a ≤ 32 := (Nat.le_of_dvd Nat.card_pos hdiv).trans (by omega)
  have ha : a ≤ 5 := by
    by_contra hn
    have hp : 64 ≤ 2 ^ a := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 6 ≤ a)
    omega
  have h16 : 16 ∣ Nat.card (fixingSubgroup P s) := by
    have hd := Subgroup.card_subgroup_dvd_card (S : Subgroup (fixingSubgroup P s))
    rcases hS with he | he
    · rwa [he] at hd
    · rw [he] at hd
      exact (by norm_num : 16 ∣ 32).trans hd
  rw [hH] at h16 ⊢
  interval_cases a <;> interval_cases b <;> norm_num at *

end FiveTransitive.Degree52FourOrders

end CFSG
