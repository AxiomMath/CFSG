module

public import CFSG.Permutation.FiveTransitive.Degree69FiveProjection
public import CFSG.Permutation.FiveTransitive.Degree69FiveCentralizer
public import CFSG.Permutation.FiveTransitive.Degree69FiveSevenLift
public import CFSG.Permutation.FiveTransitive.Degree68SevenSmallFiber

public section

namespace CFSG

namespace FiveTransitive.Degree69FiveOrder
open MulAction SylowFixedActionCore

private theorem image_card_le_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 5 Q) (hF : Nat.card (fixedPoints Q X) = 9)
    (g : FixedNormalizerAction.Normalizer Q) (hg : orderOf g = 7) :
    Nat.card Q ≤ 5 := by
  classical
  obtain ⟨T,hker,hcompat⟩ :=
    Degree69FiveProjection.exists_projection P hcard h5 hnotAlt Q hQ hF g hg
  let a := Q.normalizerMonoidHom g
  have ha : a ^ 7 = 1 := by
    rw [← map_pow,← hg,pow_orderOf_eq_one,map_one]
  have htrivial : a = 1 := Degree68SevenSmallFiber.eq_one
    (toPermHom Q T) a 7 (by decide) ha hcompat (by omega)
  apply Degree69FiveCentralizer.card_le_five P hcard h5 hnotAlt Q hQ g.val
    ((Subgroup.orderOf_coe g).trans hg)
  intro q
  have he := congrArg Subtype.val (DFunLike.congr_fun htrivial q)
  change (Q.normalizerMonoidHom g q).val = q.val at he
  rw [Q.normalizerMonoidHom_apply_apply_coe] at he
  exact (mul_inv_eq_iff_eq_mul).mp he

theorem card_le_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 5 (fixingSubgroup P s)) :
    Nat.card S ≤ 5 := by
  classical
  by_cases hS : Nat.card S = 1
  · omega
  let Q := sylowImage X P s S
  have hQ : IsPGroup 5 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hF : Nat.card (fixedPoints Q X) = 9 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact (Degree69FiveFixed.fixed_card_and_alternating P hcard h5 hnotAlt s hs S hS).1
  obtain ⟨g,hg⟩ := Degree69FiveSevenLift.exists_seven P hcard h5 hnotAlt s hs S hS
  have hQcard : Nat.card Q = Nat.card S :=
    Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective
  rw [← hQcard]
  exact image_card_le_five P hcard h5 hnotAlt Q hQ hF g hg

end FiveTransitive.Degree69FiveOrder

end CFSG
