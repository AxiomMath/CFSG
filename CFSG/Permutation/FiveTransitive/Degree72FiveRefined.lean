module

public import CFSG.Permutation.FiveTransitive.Degree72FiveFixedCases
public import CFSG.Permutation.FiveTransitive.Degree72FiveSevenExterior
public import CFSG.Permutation.FiveTransitive.Degree72FiveSevenLift

public section

namespace CFSG

namespace FiveTransitive.Degree72FiveRefined
open MulAction SylowFixedActionCore

theorem fixed_card_eq_twelve
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hseven : ∀ g : P, orderOf g = 7 → Nat.card (Function.fixedPoints g.val) = 2)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 5 (fixingSubgroup P s))
    (hS : Nat.card S ≠ 1) : Nat.card (sylowFixedPoints X P s S) = 12 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  rcases Degree72FiveFixedCases.five_fixed_card_cases P hcard h5 hnotAlt s hs S hS with hF | hF
  · let Q := sylowImage X P s S
    have hQ : IsPGroup 5 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
    have hcommon : Nat.card (fixedPoints Q X) = 7 := by
      rw [← FixedNormalizerAction.fixed_eq Q]
      exact hF
    obtain ⟨g,hg⟩ := Degree72FiveSevenLift.exists_seven P hcard h5 hnotAlt s hs S hF
    have h30 := (Degree72FiveSevenExterior.fixed_card_data P hcard h5 hnotAlt Q hQ hcommon g hg).2
    have h2 := hseven g.val ((Subgroup.orderOf_coe g).trans hg)
    omega
  · exact hF

end FiveTransitive.Degree72FiveRefined

end CFSG
