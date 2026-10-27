module

public import CFSG.Permutation.FiveTransitive.Degree67TwoFiveReduction
public import CFSG.Permutation.FiveTransitive.Degree67TwoFiveLifts
public import CFSG.Permutation.FiveTransitive.Degree67TwoFixedBound

public section

namespace CFSG

namespace FiveTransitive.Degree67TwoFiveActual
open MulAction SylowFixedActionCore NormalizerOrbitFamily

theorem easy_or_hard
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s))
    (hF : Nat.card (sylowFixedPoints X P s S) = 5) :
    Nat.card S ≤ 65536 ∨
      ((∀ x : X, Nat.card (orbit (sylowImage X P s S) x) ≤ 4) ∧
        Nat.card (Family (X := X) (sylowImage X P s S) 2) = 1 ∧
        Nat.card (Family (X := X) (sylowImage X P s S) 4) = 15) := by
  classical
  let Q := sylowImage X P s S
  have hQ : IsPGroup 2 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hQcard : Nat.card Q = Nat.card S :=
    Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective
  have hfixed : Nat.card (fixedPoints Q X) = 5 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact hF
  obtain ⟨g3,g5,hg3,hg5,h3,hfive⟩ := Degree67TwoFiveLifts.exists_normalizers P hcard h5 hnotAlt s hs S hF
  have hh := Degree67TwoFiveReduction.easy_or_hard hcard Q hQ hfixed g3 g5 hg3 hg5 h3 hfive
    (Degree67TwoFixedBound.nonidentity_fixed_le P hcard h5 hnotAlt Q)
  rwa [hQcard] at hh

end FiveTransitive.Degree67TwoFiveActual

end CFSG
