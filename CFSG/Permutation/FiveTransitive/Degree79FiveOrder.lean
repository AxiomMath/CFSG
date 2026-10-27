module

public import CFSG.Permutation.FiveTransitive.Degree79FiveProjection
public import CFSG.Permutation.FiveTransitive.Degree79FiveSevenCentralizer
public import CFSG.Permutation.FiveTransitive.SylowFixedActionCore

public section

namespace CFSG

namespace FiveTransitive.Degree79FiveOrder
open MulAction SylowFixedActionCore

theorem card_le_five_of_large_seven_fixed
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 5 Q) (hF : Nat.card (fixedPoints Q X) = 9)
    (g : FixedNormalizerAction.Normalizer Q) (hg : orderOf g = 7)
    (hbig : 10 ≤ Nat.card (Function.fixedPoints g.val.val)) : Nat.card Q ≤ 5 := by
  have he := Degree79FiveProjection.conjugation_eq_one P hcard h5 hnotAlt Q hQ hF g hg hbig
  have hd := Degree79FiveExterior.fixed_card_cases P hcard h5 hnotAlt Q hQ hF g hg
  have hfixed : Nat.card (Function.fixedPoints g.val.val) = 37 := by omega
  apply Degree79FiveSevenCentralizer.card_le_five P hcard h5 hnotAlt Q hQ g.val
    ((Subgroup.orderOf_coe g).trans hg) hfixed
  intro q
  have hh := congrArg Subtype.val (DFunLike.congr_fun he q)
  change (Q.normalizerMonoidHom g q).val = q.val at hh
  rw [Q.normalizerMonoidHom_apply_apply_coe] at hh
  exact (mul_inv_eq_iff_eq_mul).mp hh

end FiveTransitive.Degree79FiveOrder

end CFSG
