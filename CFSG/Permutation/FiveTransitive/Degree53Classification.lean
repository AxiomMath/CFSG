module

public import CFSG.Permutation.FiveTransitive.Degree53SixteenEntrance
public import CFSG.Permutation.FiveTransitive.Degree53SevenAutSection
public import CFSG.Permutation.FiveTransitive.AutSixteenNoSection

public section

namespace CFSG

namespace FiveTransitive.Degree53Classification
open MulAction FixedNormalizerAction

theorem alternatingGroup_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 53)
    (h5 : IsMultiplyPretransitive P X 5) : alternatingGroup X ≤ P := by
  by_contra hnotAlt
  obtain ⟨H,_,hH5,hHnot,_,Q,hQ,hQc,hF,him,_⟩ :=
    Degree53SixteenEntrance.exists_subgroup P hcard h5 hnotAlt
  obtain ⟨hc,hpow⟩ := Degree53SevenAutSection.elementary_of_card_sixteen
    H hcard hH5 hHnot Q hQ hF him hQc
  obtain ⟨f,hf⟩ := Degree53SevenAutSection.exists_surjective_aut_image_hom
    H hcard hH5 hHnot Q hQ hF him
  exact AutSixteenNoSection.no_surjection Q hQc hc hpow hF _ f hf

end FiveTransitive.Degree53Classification

end CFSG
