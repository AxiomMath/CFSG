module

public import CFSG.Permutation.FiveTransitive.Degree72ElevenCyclic

public section

namespace CFSG

namespace FiveTransitive.Degree72ElevenGlobal
open MulAction Subgroup SylowFixedActionCore

private theorem fixed_card_eq_six_of_five_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 11)
    (hbig : 5 ≤ Nat.card (Function.fixedPoints g.val)) :
    Nat.card (Function.fixedPoints g.val) = 6 := by
  classical
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hsize : 5 ≤ (Function.fixedPoints g.val).ncard := by rwa [← Nat.card_coe_set_eq]
  obtain ⟨s,hsub,hs⟩ := Set.exists_subset_card_eq hsize
  let H := fixingSubgroup P s
  let u : H := ⟨g,(mem_fixingSubgroup_iff P).mpr (fun x hx => hsub hx)⟩
  have hu : orderOf u = 11 := (Subgroup.orderOf_coe u).symm.trans hg
  have hZ : IsPGroup 11 (zpowers u) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers,hu,pow_one]
  obtain ⟨S,hZS⟩ := hZ.exists_le_sylow
  have hSge : 11 ≤ Nat.card S := by
    have hh := Subgroup.card_le_of_le hZS
    rwa [Nat.card_zpowers,hu] at hh
  have hSne : Nat.card S ≠ 1 := by omega
  let Q := sylowImage X P s S
  have hQcard : Nat.card Q = Nat.card S := Subgroup.card_map_of_injective H.subtype_injective
  have hQbound : Nat.card Q ≤ 11 := by
    rw [hQcard]
    exact le_of_eq (Degree72ElevenCyclic.card_eq_eleven P hcard h5 hnotAlt s hs S hSne)
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
  exact Degree72ElevenFixed.fixed_card_eq_six P hcard h5 hnotAlt s hs S hSne

theorem fixed_card_eq_six
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 11) :
    Nat.card (Function.fixedPoints g.val) = 6 := by
  classical
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  apply fixed_card_eq_six_of_five_le P hcard h5 hnotAlt g hg
  let a : Function.End X := g.val.toFun
  have ha : a ^ 11 = 1 := by
    funext x
    change (g ^ 11).val x = x
    rw [← hg,pow_orderOf_eq_one]
    rfl
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 11) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card X % 11 = Fintype.card (Function.fixedPoints g.val) % 11 at hm
  rw [hcard,← Nat.card_eq_fintype_card] at hm
  omega

end FiveTransitive.Degree72ElevenGlobal

end CFSG
