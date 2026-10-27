module

public import CFSG.Permutation.FiveTransitive.FixedSetNormalizerPerm
public import CFSG.Permutation.FiveTransitive.SixPointEvenOrderFour
public import Mathlib.Data.Set.Card

public section

namespace CFSG

namespace FiveTransitive.SixFixedNormalizerSquare

open MulAction FixedSetNormalizerPerm

theorem square_fixes_common_fixed_set
    (G X : Type*) [Group G] [Fintype X] [MulAction G X]
    (Q : Subgroup G) (a : G) (ha : a ∈ Subgroup.normalizer (Q : Set G))
    (hcard : (fixedPoints Q X).ncard = 6) (ha4 : a ^ 4 = 1)
    (hnoNew : ∀ x : X, a ^ 2 • x = x → a • x = x)
    (heven : letI := Fintype.ofFinite (fixedPoints Q X)
      letI := Classical.decEq (fixedPoints Q X)
      (fixedPerm G X Q a ha).sign = 1) :
    ∀ x ∈ fixedPoints Q X, a ^ 2 • x = x := by
  classical
  let _ := Fintype.ofFinite (fixedPoints Q X)
  let _ : DecidableEq (fixedPoints Q X) := Classical.decEq _
  let f := fixedPerm G X Q a ha
  have hf4 : f ^ 4 = 1 := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    rw [fixedPerm_pow_apply_val, ha4, one_smul]
    rfl
  have hf2 : f ^ 2 = 1 := by
    by_contra hne
    obtain ⟨x, hx2, hx⟩ := SixPointEvenOrderFour.exists_fixed_square_not_fixed
      (fixedPoints Q X) (by simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using hcard)
      f heven hf4 hne
    apply hx
    apply Subtype.ext
    exact hnoNew x.val (by
      have h := congrArg Subtype.val hx2
      simpa only [f, fixedPerm_pow_apply_val] using h)
  intro x hx
  have h := congrArg (fun q : Equiv.Perm (fixedPoints Q X) => (q ⟨x, hx⟩).val) hf2
  simpa only [f, fixedPerm_pow_apply_val, Equiv.Perm.one_apply] using h

end FiveTransitive.SixFixedNormalizerSquare

end CFSG
