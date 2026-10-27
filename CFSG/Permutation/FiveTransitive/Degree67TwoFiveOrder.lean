module

public import CFSG.Permutation.FiveTransitive.Degree67TwoFiveActual
public import CFSG.Permutation.FiveTransitive.Degree67TwoHardBound

public section

namespace CFSG

namespace FiveTransitive.Degree67TwoFiveOrder
open MulAction SylowFixedActionCore

theorem card_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s))
    (hF : Nat.card (sylowFixedPoints X P s S) = 5) : Nat.card S ≤ 65536 := by
  classical
  rcases Degree67TwoFiveActual.easy_or_hard P hcard h5 hnotAlt s hs S hF with h | ⟨horbit,hpair,hquad⟩
  · exact h
  let Q := sylowImage X P s S
  have hQ : IsPGroup 2 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hQcard : Nat.card Q = Nat.card S :=
    Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective
  have hfixed : Nat.card (fixedPoints Q X) = 5 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact hF
  rw [← hQcard]
  exact Degree67TwoHardBound.card_le hcard Q hQ hfixed horbit hpair.ge
    ((show 4 ≤ 15 by decide).trans hquad.ge)
    (Degree67TwoFixedBound.nonidentity_fixed_le P hcard h5 hnotAlt Q)

end FiveTransitive.Degree67TwoFiveOrder

end CFSG
