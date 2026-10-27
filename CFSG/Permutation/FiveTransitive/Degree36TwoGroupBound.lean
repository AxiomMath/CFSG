module

public import CFSG.Permutation.FiveTransitive.Degree36InvolutionSupport

public section

namespace CFSG

namespace FiveTransitive.Degree36TwoGroupBound

open MulAction

theorem fixed_card_le_sixteen
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 2 Q) (q : Q) (hq : q ≠ 1) :
    Nat.card (fixedBy X q) ≤ 16 := by
  obtain ⟨a,ha⟩ := IsPGroup.iff_orderOf.mp hQ q
  have ha0 : 0 < a := by
    by_contra hn
    have he : orderOf q = 1 := by simpa only [show a = 0 by omega,pow_zero] using ha
    exact hq (orderOf_eq_one_iff.mp he)
  have hd : 2 ∣ orderOf q := by
    rw [ha]
    exact pow_dvd_pow 2 ha0
  let w : Q := q ^ (orderOf q / 2)
  have hw : orderOf w.val = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos q)) hd
  have hb := Degree36InvolutionSupport.fixed_card_le_sixteen P hcard h5 hnotAlt w.val hw
  have hsub : fixedBy X q ⊆ fixedBy X w.val := by
    intro x hx
    exact (stabilizer Q x).pow_mem hx _
  have hle : Nat.card (fixedBy X q) ≤ Nat.card (fixedBy X w.val) := by
    simpa only [← Nat.card_coe_set_eq] using Set.ncard_le_ncard hsub
  exact hle.trans hb

end FiveTransitive.Degree36TwoGroupBound

end CFSG
