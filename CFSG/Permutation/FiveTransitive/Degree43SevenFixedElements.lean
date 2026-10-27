module

public import CFSG.Permutation.FiveTransitive.Degree43SevenOrder
public import CFSG.Permutation.FiveTransitive.CentralizingSingletonFixed

public section

namespace CFSG

namespace FiveTransitive.Degree43SevenFixedElements

open MulAction Subgroup SylowFixedActionCore

theorem fixed_card_eq_eight
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 43)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 7) (hfixed : 5 ≤ Nat.card (Function.fixedPoints g.val)) :
    Nat.card (Function.fixedPoints g.val) = 8 := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hn : 5 ≤ (Function.fixedPoints g.val).ncard := by rw [← Nat.card_coe_set_eq]; exact hfixed
  obtain ⟨s,hsub,hs⟩ := Set.exists_subset_card_eq hn
  let H := fixingSubgroup P s
  let u : H := ⟨g,(mem_fixingSubgroup_iff P).mpr (fun x hx => hsub hx)⟩
  have hu : orderOf u = 7 := (Subgroup.orderOf_coe u).symm.trans hg
  have hZ : IsPGroup 7 (zpowers u) := by
    apply IsPGroup.of_card
    rw [Nat.card_zpowers,hu,pow_one]
  obtain ⟨S,hZS⟩ := hZ.exists_le_sylow
  have hSge : 7 ≤ Nat.card S := by
    have h := Subgroup.card_le_of_le hZS
    rwa [Nat.card_zpowers,hu] at h
  have hS : Nat.card S ≠ 1 := by omega
  have hScard := Degree43SevenOrder.card_eq_seven P hcard h5 hnotAlt s hs S hS
  let Q := sylowImage X P s S
  have hQcard : Nat.card Q = 7 := by
    have h : Nat.card Q = Nat.card S := Nat.card_congr
      ((S : Subgroup H).equivMapOfInjective H.subtype Subtype.val_injective).toEquiv.symm
    exact h.trans hScard
  have hRQ : zpowers g = Q := by
    apply Subgroup.eq_of_le_of_card_ge
    · apply zpowers_le.mpr
      exact ⟨u,hZS (mem_zpowers u),rfl⟩
    · rw [Nat.card_zpowers,hg,hQcard]
  have hF := (Degree43SevenFixed.fixed_card_and_image P hcard h5 hnotAlt s hs S hS).1
  have hfixeq : (sylowFixedPoints X P s S : Set X) = fixedPoints Q X :=
    FixedNormalizerAction.fixed_eq Q
  change Nat.card (fixedBy X g) = 8
  rw [← CentralizingSingletonFixed.fixed_zpowers,hRQ,← hfixeq]
  exact hF

end FiveTransitive.Degree43SevenFixedElements

end CFSG
