module

public import CFSG.Permutation.FiveTransitive.Degree60ThreeConditional
public import CFSG.Permutation.FiveTransitive.Degree60ThreeElevenLift
public import CFSG.Permutation.FiveTransitive.Degree60ThreeOrbitGeometry
public import CFSG.Permutation.FiveTransitive.Degree60ThreeOrbitSharpBound
public import CFSG.Permutation.FiveTransitive.Degree60ThreeNineBound

public section

namespace CFSG

namespace FiveTransitive.Degree60ThreeBoundCore

open MulAction SylowFixedActionCore

private theorem card_le_243_of_fixed_twelve
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 60)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 3 (fixingSubgroup P s))
    (hF12 : Nat.card (sylowFixedPoints X P s S) = 12) : Nat.card S ≤ 243 := by
  classical
  let Q := sylowImage X P s S
  have hQ : IsPGroup 3 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hfixed : Nat.card (fixedPoints Q X) = 12 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact hF12
  obtain ⟨g,hg,hgfixed⟩ := Degree60ThreeElevenLift.exists_eleven_fixed_sixteen
    P hcard h5 hnotAlt s hs S hF12
  have hgfixed' : Nat.card (fixedBy X g) = 16 := hgfixed
  have hX : Nat.card X = 60 := by rwa [Nat.card_eq_fintype_card]
  have hQbound : Nat.card Q ≤ 243 := by
    by_cases h9 : ∃ x : X, Nat.card (orbit Q x) = 9
    · obtain ⟨x,hx⟩ := h9
      exact Degree60ThreeNineBound.card_le_243 P hcard h5 hnotAlt Q hQ hfixed x hx
        (Degree60ThreeOrbitGeometry.orbit_card_le_three_outside_nine hX Q hQ g hg hgfixed' x hx)
    · have horbit : ∀ x : X, x ∉ fixedPoints Q X → Nat.card (orbit Q x) = 3 := by
        intro x hx
        rcases Degree60ThreeOrbitGeometry.orbit_card_cases hX Q hQ g hg hgfixed' x hx with h | h
        · exact h
        · exact (h9 ⟨x,h⟩).elim
      have h := Degree60ThreeOrbitSharpBound.card_le_eighty_one P hcard h5 hnotAlt Q hQ hfixed horbit
      omega
  have heq : Nat.card Q = Nat.card S := Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective
  rwa [heq] at hQbound

theorem card_le_243_of_five_fixed_cases
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 60)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hfive : ∀ g : P, orderOf g = 5 → Nat.card (Function.fixedPoints g.val) = 0 ∨ Nat.card (Function.fixedPoints g.val) = 5)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 3 (fixingSubgroup P s)) : Nat.card S ≤ 243 := by
  by_cases hS : Nat.card S = 1
  · omega
  have hF := Degree60ThreeConditional.fixed_card_eq_twelve_of_five_fixed_cases
    P hcard h5 hnotAlt hfive s hs S hS
  exact card_le_243_of_fixed_twelve P hcard h5 hnotAlt s hs S hF

end FiveTransitive.Degree60ThreeBoundCore

end CFSG
