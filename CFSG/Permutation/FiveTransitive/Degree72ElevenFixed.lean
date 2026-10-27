module

public import CFSG.Permutation.FiveTransitive.Degree72LargePrimeCases

public section

namespace CFSG

namespace FiveTransitive.Degree72ElevenFixed
open MulAction SylowFixedActionCore

theorem fixed_card_eq_six
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 11 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    Nat.card (sylowFixedPoints X P s S) = 6 := by
  have h := Degree72LargePrimeCases.fixed_card_cases 11 (by decide) (Or.inl rfl)
    P hcard h5 hnotAlt s hs S hS
  omega

theorem image_eq_top
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 11 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    (toPermHom (sylowNormalizer X P s S) (sylowFixedPoints X P s S)).range = ⊤ := by
  classical
  let F := sylowFixedPoints X P s S
  let N := sylowNormalizer X P s S
  let J := (toPermHom N F).range
  have hf := fixed_card_eq_six P hcard h5 hnotAlt s hs S hS
  have hN5 := (Degree72LargePrimeFixed.bounds_and_transitive 11 (by decide) P hcard h5 hnotAlt s hs S hS).2.2
  have hJ5 : IsMultiplyPretransitive J F 5 := by
    constructor
    intro a b
    obtain ⟨g,hg⟩ := hN5.exists_smul_eq a b
    exact ⟨⟨toPermHom N F g,⟨g,rfl⟩⟩,hg⟩
  apply Equiv.Perm.eq_top_of_isMultiplyPretransitive
  simpa only [F,hf] using hJ5

end FiveTransitive.Degree72ElevenFixed

end CFSG
