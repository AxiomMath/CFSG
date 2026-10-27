module

public import CFSG.Permutation.FiveTransitive.TwoPrimeCycleEntrance
public import CFSG.Permutation.FiveTransitive.TwoPrimeCycleCentralizer

public section

namespace CFSG

namespace FiveTransitive.TwoPrimeCycleClassification

open MulAction

theorem alternatingGroup_le
    {X : Type} [Fintype X] [DecidableEq X]
    (p f : ℕ) (hp : p.Prime) (hp13 : 13 ≤ p) (hf : f = 3 ∨ f = 4)
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 2 * p + f)
    (h5 : IsMultiplyPretransitive P X 5) : alternatingGroup X ≤ P := by
  by_contra hnotAlt
  obtain ⟨u,_,htype,hfixed,himage⟩ :=
    TwoPrimeCycleEntrance.exists_generator p f hp hp13 hf P hcard h5 hnotAlt
  exact TwoPrimeCycleCentralizer.excluded p f hp hp13 hf P hcard h5 hnotAlt u htype hfixed himage

theorem subgroup_card_classification
    {X : Type} [Fintype X] [DecidableEq X]
    (p f : ℕ) (hp : p.Prime) (hp13 : 13 ≤ p) (hf : f = 3 ∨ f = 4)
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 2 * p + f)
    (h5 : IsMultiplyPretransitive P X 5) :
    Nat.card P = (Fintype.card X).factorial ∨
      (7 ≤ Fintype.card X ∧ Nat.card P = (Fintype.card X).factorial / 2) := by
  rcases FiveTransitive.alt_le_perm_card_dichotomy X P (by omega)
    (alternatingGroup_le p f hp hp13 hf P hcard h5) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨by omega,h⟩

end FiveTransitive.TwoPrimeCycleClassification

end CFSG
