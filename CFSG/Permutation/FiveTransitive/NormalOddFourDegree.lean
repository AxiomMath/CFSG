module

public import CFSG.Permutation.FiveTransitive.NormalAlternatingFixer
public import CFSG.Permutation.FiveTransitive.SmallDegreeClassification

public section

namespace CFSG

namespace FiveTransitive.NormalOddFourDegree
open MulAction Subgroup

theorem nontrivial_of_four_transitive
    (G X : Type) [Group G] [Fintype X] [MulAction G X]
    (hn : 4 ≤ Nat.card X) (h4 : IsMultiplyPretransitive G X 4) : Nontrivial G := by
  let _ : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : IsMultiplyPretransitive G X 4 := h4
  have h1 : IsMultiplyPretransitive G X 1 :=
    isMultiplyPretransitive_of_le (G := G) (α := X) (n := 4) (by omega) hn
  let _ : IsPretransitive G X := is_one_pretransitive_iff.mp h1
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  obtain ⟨g, hg⟩ := exists_smul_eq G x y
  exact ⟨⟨g, 1, fun he => hxy (by simpa [he] using hg)⟩⟩

theorem symmetric_or_alternating_of_card
    (X : Type) [Fintype X] [DecidableEq X] (hn : 2 ≤ Nat.card X)
    (P : Subgroup (Equiv.Perm X))
    (hP : Nat.card P = (Fintype.card X).factorial ∨
      Nat.card P = (Fintype.card X).factorial / 2) :
    P = ⊤ ∨ P = alternatingGroup X := by
  have hperm : Nat.card (Equiv.Perm X) = (Fintype.card X).factorial := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card]
  rcases hP with htop | halt
  · exact Or.inl (Subgroup.eq_top_of_card_eq P (htop.trans hperm.symm))
  · right
    apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := P))
    rw [P.index_mul_card, hperm, halt]
    symm
    apply Nat.mul_div_cancel'
    have h := Nat.factorial_dvd_factorial hn
    simpa only [Nat.card_eq_fintype_card, Nat.factorial_two] using h

theorem degree_cases
    (X : Type) [Fintype X] [DecidableEq X]
    (P L : Subgroup (Equiv.Perm X)) (hLP : L ≤ P)
    [(L.subgroupOf P).Normal]
    (hn : Fintype.card X ≤ 27)
    (hP5 : IsMultiplyPretransitive P X 5)
    (hL4 : IsMultiplyPretransitive L X 4)
    (s : Set X) (hs : s.ncard = 4)
    (hodd : ¬ 2 ∣ Nat.card (fixingSubgroup L s)) :
    Fintype.card X ≤ 7 ∨ Fintype.card X = 12 ∨ Fintype.card X = 24 := by
  by_cases hsmall : Fintype.card X ≤ 7
  · exact Or.inl hsmall
  have hlarge : 8 ≤ Nat.card X := by rw [Nat.card_eq_fintype_card]; omega
  let _ : Nontrivial L := nontrivial_of_four_transitive L X (by omega) hL4
  let _ : Nontrivial (L.subgroupOf P) := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLP).toEquiv]
    exact Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  rcases SmallDegreeClassification.subgroup_card_classification X P (by omega) hn hP5 with
    hsym | ⟨_, halt⟩ | ⟨h12, _⟩ | ⟨h24, _⟩
  · have hshape := symmetric_or_alternating_of_card X (by omega) P (Or.inl hsym)
    have hAlt := NormalAlternatingFixer.alternating_le_normal_image X (by omega) P hshape (L.subgroupOf P)
    rw [Subgroup.map_subgroupOf_eq_of_le hLP] at hAlt
    exact (hodd (NormalAlternatingFixer.two_dvd_four_fixer_of_alternating_le X hlarge L hAlt s hs)).elim
  · have hshape := symmetric_or_alternating_of_card X (by omega) P (Or.inr halt)
    have hAlt := NormalAlternatingFixer.alternating_le_normal_image X (by omega) P hshape (L.subgroupOf P)
    rw [Subgroup.map_subgroupOf_eq_of_le hLP] at hAlt
    exact (hodd (NormalAlternatingFixer.two_dvd_four_fixer_of_alternating_le X hlarge L hAlt s hs)).elim
  · exact Or.inr (Or.inl h12)
  · exact Or.inr (Or.inr h24)

end FiveTransitive.NormalOddFourDegree

end CFSG
