module

public import CFSG.Permutation.FiveTransitive.Degree68FiveOrder

public section

namespace CFSG

namespace FiveTransitive.Degree68FiveGlobal
open MulAction Subgroup SylowFixedActionCore

private theorem fixed_card_eq_eight_of_five_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 68)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 5)
    (hbig : 5 ≤ Nat.card (Function.fixedPoints g.val)) :
    Nat.card (Function.fixedPoints g.val) = 8 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hsize : 5 ≤ (Function.fixedPoints g.val).ncard := by rwa [← Nat.card_coe_set_eq]
  obtain ⟨s,hsub,hs⟩ := Set.exists_subset_card_eq hsize
  let H := fixingSubgroup P s
  let u : H := ⟨g,(mem_fixingSubgroup_iff P).mpr (fun x hx => hsub hx)⟩
  have hu : orderOf u = 5 := (Subgroup.orderOf_coe u).symm.trans hg
  have hZ : IsPGroup 5 (zpowers u) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers,hu,pow_one]
  obtain ⟨S,hZS⟩ := hZ.exists_le_sylow
  have hSge : 5 ≤ Nat.card S := by
    have hh := Subgroup.card_le_of_le hZS
    rwa [Nat.card_zpowers,hu] at hh
  have hSne : Nat.card S ≠ 1 := by omega
  let Q := sylowImage X P s S
  have hQcard : Nat.card Q = Nat.card S := Subgroup.card_map_of_injective H.subtype_injective
  have hQbound : Nat.card Q ≤ 5 := by
    rw [hQcard]
    exact Degree68FiveOrder.card_le_five P hcard h5 hnotAlt s hs S
  have hRQ : zpowers g = Q := by
    apply Subgroup.eq_of_le_of_card_ge
    · apply zpowers_le.mpr
      exact ⟨u,hZS (mem_zpowers u),rfl⟩
    · rwa [Nat.card_zpowers,hg]
  have hfixeq : Function.fixedPoints g.val = fixedPoints (zpowers g) X := by
    ext x
    constructor
    · intro hx z
      have hh : zpowers g ≤ stabilizer P x := zpowers_le.mpr hx
      exact hh z.property
    · intro hx
      exact hx ⟨g,mem_zpowers g⟩
  rw [hfixeq,hRQ,← FixedNormalizerAction.fixed_eq Q]
  exact (Degree68FiveFixed.fixed_card_and_alternating P hcard h5 hnotAlt s hs S hSne).1

theorem fixed_card_cases
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 68)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 5) :
    Nat.card (Function.fixedPoints g.val) = 3 ∨ Nat.card (Function.fixedPoints g.val) = 8 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  by_cases hbig : 5 ≤ Nat.card (Function.fixedPoints g.val)
  · exact Or.inr (fixed_card_eq_eight_of_five_le P hcard h5 hnotAlt g hg hbig)
  let a : Function.End X := g.val.toFun
  have ha : a ^ 5 = 1 := by
    funext x
    change (g ^ 5).val x = x
    rw [← hg,pow_orderOf_eq_one]
    rfl
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 5) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card X % 5 = Fintype.card (Function.fixedPoints g.val) % 5 at hm
  rw [hcard,← Nat.card_eq_fintype_card] at hm
  exact Or.inl (by omega)

theorem fixed_card_le_eight
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 68)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 5) : Nat.card (Function.fixedPoints g.val) ≤ 8 := by
  have hh := fixed_card_cases P hcard h5 hnotAlt g hg
  omega

end FiveTransitive.Degree68FiveGlobal

end CFSG
