module

public import CFSG.Permutation.FiveTransitive.Degree79TwoFiveGeometry
public import CFSG.Permutation.FiveTransitive.Degree79TwoFiveLifts
public import CFSG.Permutation.FiveTransitive.Degree79TwoFixedBound
public import CFSG.Permutation.FiveTransitive.Degree79TwoGeometryBound

public section

namespace CFSG

namespace FiveTransitive.Degree79TwoFiveOrder
open MulAction SylowFixedActionCore

theorem card_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s))
    (hF : Nat.card (sylowFixedPoints X P s S) = 5) : Nat.card S ≤ 2^22 := by
  classical
  let Q := sylowImage X P s S
  have hQ : IsPGroup 2 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hQcard : Nat.card Q = Nat.card S :=
    Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective
  have hfixed : Nat.card (fixedPoints Q X) = 5 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact hF
  obtain ⟨g3,g5,hg3,hg5,h3,hfive⟩ :=
    Degree79TwoFiveLifts.exists_normalizers P hcard h5 hnotAlt s hs S hF
  have hgeometry := Degree79TwoFiveGeometry.geometry
    (by rwa [Nat.card_eq_fintype_card] : Nat.card X = 79) Q hQ hfixed
    g3 g5 hg3 hg5 h3 hfive
  rw [← hQcard]
  exact Degree79TwoGeometryBound.card_le hcard Q hQ hfixed
    (Degree79TwoFixedBound.nonidentity_fixed_le P hcard h5 hnotAlt Q) hgeometry

end FiveTransitive.Degree79TwoFiveOrder

end CFSG
