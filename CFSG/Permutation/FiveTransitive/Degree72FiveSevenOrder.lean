module

public import CFSG.Permutation.FiveTransitive.Degree72FiveSevenProjection
public import CFSG.Permutation.FiveTransitive.Degree72FiveSevenCentralizer
public import CFSG.Permutation.FiveTransitive.Degree72FiveSevenLift

public section

namespace CFSG

namespace FiveTransitive.Degree72FiveSevenOrder
open MulAction SylowFixedActionCore

theorem sylow_card_le_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 5 (fixingSubgroup P s))
    (hF7 : Nat.card (sylowFixedPoints X P s S) = 7) : Nat.card S ≤ 5 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let Q := sylowImage X P s S
  have hQ : IsPGroup 5 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hF : Nat.card (fixedPoints Q X) = 7 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact hF7
  obtain ⟨g,hg⟩ := Degree72FiveSevenLift.exists_seven P hcard h5 hnotAlt s hs S hF7
  have he := Degree72FiveSevenProjection.conjugation_eq_one P hcard h5 hnotAlt Q hQ hF g hg
  have hfixed := (Degree72FiveSevenExterior.fixed_card_data P hcard h5 hnotAlt Q hQ hF g hg).2
  have hcomm : ∀ q : Q, g.val * q.val = q.val * g.val := by
    intro q
    have hh := congrArg Subtype.val (DFunLike.congr_fun he q)
    change (Q.normalizerMonoidHom g q).val = q.val at hh
    rw [Q.normalizerMonoidHom_apply_apply_coe] at hh
    exact (mul_inv_eq_iff_eq_mul).mp hh
  have hb := Degree72FiveSevenCentralizer.card_le_five P hcard h5 hnotAlt Q hQ g.val
    ((Subgroup.orderOf_coe g).trans hg) hfixed hcomm
  have hc : Nat.card Q = Nat.card S := Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective
  rwa [hc] at hb

end FiveTransitive.Degree72FiveSevenOrder

end CFSG
