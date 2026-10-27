module

public import CFSG.Permutation.FiveTransitive.NormalOddFourDegree
public import CFSG.Permutation.FiveTransitive.Reduction

public section

namespace CFSG

namespace FiveTransitive.SmallNormalFourImage
open MulAction Subgroup

private theorem card_eq_half_factorial_of_odd_four_fixer
    (X : Type) [Fintype X] [DecidableEq X]
    (L : Subgroup (Equiv.Perm X)) (h4 : IsMultiplyPretransitive L X 4)
    (hsmall : Fintype.card X = 6 ∨ Fintype.card X = 7)
    (hAlt : alternatingGroup X ≤ L)
    (s : Set X) (hs : s.ncard = 4)
    (hodd : ¬ 2 ∣ Nat.card (fixingSubgroup L s)) :
    Nat.card L = (Fintype.card X).factorial / 2 := by
  rcases FiveTransitive.alt_le_perm_card_dichotomy X L (by omega) hAlt with htop | halt
  · have hi := h4.index_of_fixingSubgroup_mul hs
    have hc := (fixingSubgroup L s).index_mul_card
    rw [htop, ← Nat.card_eq_fintype_card] at hc
    have hfix : Nat.card (fixingSubgroup L s) = (Nat.card X - 4).factorial := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (show (fixingSubgroup L s).index ≠ 0 from Subgroup.index_ne_zero_of_finite))
      exact hc.trans hi.symm
    apply (hodd ?_).elim
    rw [hfix, Nat.card_eq_fintype_card]
    rcases hsmall with h | h <;> rw [h] <;> norm_num
  · exact halt

theorem degree_order_pairs
    (X : Type) [Fintype X] [DecidableEq X]
    (J L : Subgroup (Equiv.Perm X)) (hLJ : L ≤ J) [(L.subgroupOf J).Normal]
    (hlower : 4 ≤ Fintype.card X) (hupper : Fintype.card X ≤ 7)
    (hJ5 : IsMultiplyPretransitive J X 5) (hL4 : IsMultiplyPretransitive L X 4)
    (s : Set X) (hs : s.ncard = 4)
    (hodd : ¬ 2 ∣ Nat.card (fixingSubgroup L s)) :
    (Fintype.card X = 4 ∧ Nat.card L = 24) ∨
      (Fintype.card X = 5 ∧ Nat.card L = 120) ∨
      (Fintype.card X = 6 ∧ Nat.card L = 360) ∨
      (Fintype.card X = 7 ∧ Nat.card L = 2520) := by
  have hcases : Fintype.card X = 4 ∨ Fintype.card X = 5 ∨
      Fintype.card X = 6 ∨ Fintype.card X = 7 := by omega
  have htop (hn : Fintype.card X ≤ 5) : L = ⊤ := by
    let _ : IsMultiplyPretransitive L X 4 := hL4
    apply Equiv.Perm.eq_top_of_isMultiplyPretransitive
    apply isMultiplyPretransitive_of_le (G := L) (α := X) (n := 4)
    · rw [Nat.card_eq_fintype_card]; omega
    · simpa only [Nat.card_eq_fintype_card] using hlower
  rcases hcases with hfour | hfive | hsix | hseven
  · exact Or.inl ⟨hfour, by rw [htop (by omega), Subgroup.card_top, Nat.card_perm,
      Nat.card_eq_fintype_card, hfour]; norm_num⟩
  · exact Or.inr (Or.inl ⟨hfive, by rw [htop (by omega), Subgroup.card_top, Nat.card_perm,
      Nat.card_eq_fintype_card, hfive]; norm_num⟩)
  · have hAlt : alternatingGroup X ≤ L := by
      apply IsMultiplyPretransitive.alternatingGroup_le X L
      simpa only [Nat.card_eq_fintype_card, hsix] using hL4
    have hc := card_eq_half_factorial_of_odd_four_fixer X L hL4 (Or.inl hsix) hAlt s hs hodd
    exact Or.inr (Or.inr (Or.inl ⟨hsix, by norm_num [hsix] at hc; exact hc⟩))
  · have hAltJ : alternatingGroup X ≤ J := by
      apply IsMultiplyPretransitive.alternatingGroup_le X J
      simpa only [Nat.card_eq_fintype_card, hseven] using hJ5
    have hshape : J = ⊤ ∨ J = alternatingGroup X := by
      apply NormalOddFourDegree.symmetric_or_alternating_of_card X (by rw [Nat.card_eq_fintype_card, hseven]; omega) J
      exact FiveTransitive.alt_le_perm_card_dichotomy X J (by omega) hAltJ
    let _ : Nontrivial L := NormalOddFourDegree.nontrivial_of_four_transitive L X
      (by rw [Nat.card_eq_fintype_card]; omega) hL4
    let _ : Nontrivial (L.subgroupOf J) := by
      apply Finite.one_lt_card_iff_nontrivial.mp
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLJ).toEquiv]
      exact Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    have hAlt := NormalAlternatingFixer.alternating_le_normal_image X
      (by rw [Nat.card_eq_fintype_card]; omega) J hshape (L.subgroupOf J)
    rw [Subgroup.map_subgroupOf_eq_of_le hLJ] at hAlt
    have hc := card_eq_half_factorial_of_odd_four_fixer X L hL4 (Or.inr hseven) hAlt s hs hodd
    exact Or.inr (Or.inr (Or.inr ⟨hseven, by norm_num [hseven] at hc; exact hc⟩))

end FiveTransitive.SmallNormalFourImage

end CFSG
