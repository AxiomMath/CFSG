module

public import CFSG.Permutation.FiveTransitive.Degree52FinalOrders
public import CFSG.Permutation.FiveTransitive.Degree52TwoOddActual
public import CFSG.Permutation.FiveTransitive.EvenFiveFixerHalf

public section

namespace CFSG

namespace FiveTransitive.Degree52Classification
open MulAction

private theorem exists_odd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ∃ g : fixingSubgroup P s, Equiv.Perm.sign g.val.val = -1 := by
  let S : Sylow 2 (fixingSubgroup P s) := Sylow.nonempty.some
  have hS := Degree52FinalOrders.sylow_card P hcard h5 hnotAlt s hs S
  obtain ⟨g,hg⟩ := Degree52TwoOddActual.exists_odd_five_fixer P hcard h5 hnotAlt s hs S hS
  refine ⟨g,?_⟩
  rcases Int.units_eq_one_or (Equiv.Perm.sign g.val.val) with he | ho
  · exact (hg (Equiv.Perm.mem_alternatingGroup.mpr he)).elim
  · exact ho

theorem alternatingGroup_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) : alternatingGroup X ≤ P := by
  classical
  by_contra hnotAlt
  let E : Subgroup (Equiv.Perm X) := P ⊓ alternatingGroup X
  have hE5 : IsMultiplyPretransitive E X 5 :=
    EvenFiveFixerHalf.five_transitive P h5 (exists_odd_five_fixer P hcard h5 hnotAlt)
  have hEnot : ¬ alternatingGroup X ≤ E := fun h => hnotAlt (h.trans inf_le_left)
  obtain ⟨s,_,hs⟩ := Set.exists_subset_card_eq
    (show 5 ≤ (Set.univ : Set X).ncard by simp [Set.ncard_univ,hcard])
  obtain ⟨g,hg⟩ := exists_odd_five_fixer E hcard hE5 hEnot s hs
  have he : Equiv.Perm.sign g.val.val = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp g.val.property.2
  rw [he] at hg
  norm_num at hg

end FiveTransitive.Degree52Classification

end CFSG
