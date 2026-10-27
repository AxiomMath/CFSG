module

public import CFSG.Permutation.FiveTransitive.HighDegreeMinimalSupport
public import CFSG.Permutation.FiveTransitive.FourTransitiveSupportBound

public section

namespace CFSG

namespace FiveTransitive.HighDegreeHalfSupport

open Equiv

private theorem degree_le_two_mul_support_add_three
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (hn : 28 ≤ Fintype.card X)
    (h5 : MulAction.IsMultiplyPretransitive P X 5)
    (hnotAlt : ¬ alternatingGroup X ≤ P)
    {g : Perm X} (hg : g ∈ P) (hne : g ≠ 1) :
    Fintype.card X ≤ 2 * g.support.card + 3 := by
  classical
  let _ : Fintype P := Fintype.ofFinite P
  let S := Finset.univ.filter (fun u : P => (u : Perm X) ≠ 1)
  have hS : S.Nonempty := ⟨⟨g, hg⟩, by simp [S, hne]⟩
  obtain ⟨u, hu, hmin⟩ := Finset.exists_min_image S (fun u : P => (u : Perm X).support.card) hS
  have hune : (u : Perm X) ≠ 1 := (Finset.mem_filter.mp hu).2
  have hminimal : ∀ v : Perm X, v ∈ P → v ≠ 1 → (u : Perm X).support.card ≤ v.support.card := by
    intro v hv hvne
    exact hmin ⟨v, hv⟩ (by simp [S, hvne])
  let _ : MulAction.IsMultiplyPretransitive P X 5 := h5
  have h4 : MulAction.IsMultiplyPretransitive P X 4 :=
    MulAction.isMultiplyPretransitive_of_le (G := P) (α := X) (m := 4) (n := 5)
      (by omega) (by simpa only [Nat.card_eq_fintype_card] using (show 5 ≤ Fintype.card X by omega))
  have hm := HighDegreeMinimalSupport.nine_le_support P hn h5 hnotAlt u.property hune
  have hb := FourTransitiveSupportBound.bound_of_four_transitive P h4 u u.property hminimal hm
  have hle := hminimal g hg hne
  omega

theorem alternatingGroup_le_of_nontrivial_support_le_twelve
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (hn : 28 ≤ Fintype.card X)
    (h5 : MulAction.IsMultiplyPretransitive P X 5)
    {g : Perm X} (hg : g ∈ P) (hne : g ≠ 1) (hsmall : g.support.card ≤ 12) :
    alternatingGroup X ≤ P := by
  by_contra hnotAlt
  have h := degree_le_two_mul_support_add_three P hn h5 hnotAlt hg hne
  omega

end FiveTransitive.HighDegreeHalfSupport

end CFSG
