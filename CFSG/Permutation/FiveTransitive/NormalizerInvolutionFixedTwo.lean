module

public import CFSG.Permutation.FiveTransitive.FixedSetNormalizerPerm
public import CFSG.Permutation.FiveTransitive.EvenSixInvolution

public section

namespace CFSG

namespace FiveTransitive.NormalizerInvolutionFixedTwo

open MulAction FixedSetNormalizerPerm

def fixedIntersectionEquiv
    (G X : Type*) [Group G] [MulAction G X] (Q : Subgroup G)
    (a : G) (ha : a ∈ Subgroup.normalizer (Q : Set G)) :
    Function.fixedPoints (fixedPerm G X Q a ha) ≃ ↥(fixedBy X a ∩ fixedPoints Q X) where
  toFun x := ⟨x.val.val, ⟨congrArg Subtype.val x.property, x.val.property⟩⟩
  invFun x := ⟨⟨x.val, x.property.2⟩, Subtype.ext x.property.1⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

theorem intersection_ncard_eq_two
    (G X : Type*) [Group G] [Fintype X] [MulAction G X]
    (Q : Subgroup G) (a : G) (ha : a ∈ Subgroup.normalizer (Q : Set G))
    (hcard : (fixedPoints Q X).ncard = 6) (ha2 : a ^ 2 = 1)
    (heven : letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPerm G X Q a ha).sign = 1)
    (hmove : ∃ x ∈ fixedPoints Q X, a • x ≠ x) :
    (fixedBy X a ∩ fixedPoints Q X).ncard = 2 := by
  classical
  let _ := Fintype.ofFinite (fixedPoints Q X)
  let _ : DecidableEq (fixedPoints Q X) := Classical.decEq _
  let f := fixedPerm G X Q a ha
  have hf2 : f ^ 2 = 1 := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    rw [fixedPerm_pow_apply_val, ha2, one_smul]
    rfl
  have hfne : f ≠ 1 := by
    intro hf
    obtain ⟨x, hx, hax⟩ := hmove
    apply hax
    exact congrArg (fun g : Equiv.Perm (fixedPoints Q X) => (g ⟨x, hx⟩).val) hf
  have htwo := EvenSixInvolution.fixed_card_eq_two_of_ne_one
    (by simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using hcard)
    f hf2 heven hfne
  rw [← Nat.card_coe_set_eq]
  exact (Nat.card_congr (fixedIntersectionEquiv G X Q a ha)).symm.trans htwo

end FiveTransitive.NormalizerInvolutionFixedTwo

end CFSG
