module

public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport
public import CFSG.Permutation.FiveTransitive.AbelianOrbitEvaluation

public section

namespace CFSG

namespace FiveTransitive.Degree54TwoTwoImages

open MulAction

theorem card_le_product
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (x y : X) (hx : Nat.card (orbit Q x) = 16)
    (hy : Nat.card (orbit Q y) = 16) (hxy : y ∉ orbit Q x) :
    Nat.card Q ≤ Nat.card (toPermHom Q (orbit Q x)).range *
      Nat.card (toPermHom Q (orbit Q y)).range := by
  classical
  let fx := toPermHom Q (orbit Q x)
  let fy := toPermHom Q (orbit Q y)
  let f : Q →* fx.range × fy.range := fx.rangeRestrict.prod fy.rangeRestrict
  have hinj : Function.Injective f := by
    apply (injective_iff_map_eq_one _).mpr
    intro q hq
    by_contra hn
    have hne : q.val.val ≠ 1 := by
      intro he
      exact hn (Subtype.ext (Subtype.ext he))
    have hxq : fx q = 1 := congrArg (fun t : fx.range × fy.range => t.1.val) hq
    have hyq : fy q = 1 := congrArg (fun t : fx.range × fy.range => t.2.val) hq
    have hsub : orbit Q x ∪ orbit Q y ⊆ Function.fixedPoints q.val.val := by
      intro z hz
      rcases hz with hz | hz
      · exact congrArg (fun t : orbit Q x => t.val) (DFunLike.congr_fun hxq ⟨z,hz⟩)
      · exact congrArg (fun t : orbit Q y => t.val) (DFunLike.congr_fun hyq ⟨z,hz⟩)
    have hlow := Set.ncard_le_ncard hsub
    rw [Set.ncard_union_eq (AbelianOrbitEvaluation.orbit_disjoint_of_notMem x y hxy),
      ← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,hx,hy,
      ← Nat.card_coe_set_eq] at hlow
    have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5 hnotAlt
      q.val.property hne
    rw [hcard] at hb
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,q.val.val.sum_cycleType,hcard] at hlow
    omega
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hinj

end FiveTransitive.Degree54TwoTwoImages

end CFSG
