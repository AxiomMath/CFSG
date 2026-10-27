module

public import CFSG.Permutation.FiveTransitive.Degree72FiveOrbitGeometry
public import CFSG.Permutation.FiveTransitive.Degree72FiveGroupBound
public import CFSG.Permutation.FiveTransitive.Degree72FiveElevenCentralizer

public section

namespace CFSG

namespace FiveTransitive.Degree72FiveTwelveOrder

open MulAction Subgroup SylowFixedActionCore

theorem sylow_card_le_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s))
    (hF12 : Nat.card (sylowFixedPoints X P s S) = 12) : Nat.card S ≤ 5 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let Q := sylowImage X P s S
  have hQ : IsPGroup 5 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hfixeq : (sylowFixedPoints X P s S : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  have hF : Nat.card (fixedPoints Q X) = 12 := by rwa [← hfixeq]
  have horbit := Degree72FiveOrbitGeometry.exterior_orbit_card_five P hcard h5 hnotAlt s hs S hF12
  have hb := Degree72FiveGroupBound.card_le_625 P hcard h5 hnotAlt Q hQ hF horbit
  obtain ⟨g,hg⟩ := Degree72FiveOrbitGeometry.exists_eleven P hcard h5 hnotAlt s hs S hF12
  have haut : Q.normalizerMonoidHom g = 1 := FiveGroup625ElevenAutomorphism.eq_one hQ hb _
    (by rw [← map_pow,← hg,pow_orderOf_eq_one,map_one])
  have hcomm : ∀ q : Q, g.val * q.val = q.val * g.val := by
    intro q
    have hh : g.val * q.val * g.val⁻¹ = q.val :=
      congrArg Subtype.val (DFunLike.congr_fun haut q)
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using
      congrArg (fun a : P => a * g.val) hh
  have hsmall := Degree72FiveElevenCentralizer.card_le_five P hcard h5 hnotAlt Q hQ g.val
    ((Subgroup.orderOf_coe g).trans hg) hcomm
  have he : Nat.card Q = Nat.card S := Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective
  rwa [he] at hsmall

end FiveTransitive.Degree72FiveTwelveOrder

end CFSG
