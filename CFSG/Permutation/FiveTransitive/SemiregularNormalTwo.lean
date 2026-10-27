module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG

namespace FiveTransitive.SemiregularNormalTwo

private theorem orderOf_eq_of_ne_one
    (G X : Type*) [Group G] [MulAction G X] [Nonempty X]
    (h2 : MulAction.IsMultiplyPretransitive G X 2)
    (T : Subgroup G) [T.Normal] [IsCancelSMul T X]
    (a b : T) (ha : a ≠ 1) (hb : b ≠ 1) : orderOf a = orderOf b := by
  let x : X := Classical.choice inferInstance
  have hax : x ≠ a • x := by
    intro h
    apply ha
    exact IsCancelSMul.right_cancel a 1 x (by simpa using h.symm)
  have hbx : x ≠ b • x := by
    intro h
    apply hb
    exact IsCancelSMul.right_cancel b 1 x (by simpa using h.symm)
  obtain ⟨g, hg0, hg1⟩ := MulAction.is_two_pretransitive_iff.mp h2 hax hbx
  have hginv : g⁻¹ • x = x := by
    rw [inv_smul_eq_iff]
    exact hg0.symm
  have heq : MulAut.conjNormal (H := T) g a = b := by
    apply IsCancelSMul.right_cancel (MulAut.conjNormal (H := T) g a) b x
    change ((MulAut.conjNormal (H := T) g a : T) : G) • x = (b : G) • x
    rw [MulAut.conjNormal_apply, mul_smul, mul_smul, hginv]
    exact hg1
  exact ((MulAut.conjNormal (H := T) g).orderOf_eq a).symm.trans (congrArg orderOf heq)

private theorem exists_prime_isPGroup
    (G X : Type*) [Group G] [MulAction G X] [Nonempty X]
    (h2 : MulAction.IsMultiplyPretransitive G X 2)
    (T : Subgroup G) [T.Normal] [IsCancelSMul T X] [Finite T] [Nontrivial T] :
    ∃ p : ℕ, p.Prime ∧ IsPGroup p T := by
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (ne_of_gt (Finite.one_lt_card (α := T)))
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p hpdvd
  have ha1 : a ≠ 1 := by
    intro h
    have : p = 1 := by simpa [h] using ha.symm
    exact hp.ne_one this
  refine ⟨p, hp, IsPGroup.iff_orderOf.mpr ?_⟩
  intro b
  by_cases hb : b = 1
  · exact ⟨0, by simp [hb]⟩
  · exact ⟨1, by simpa only [pow_one] using
      (orderOf_eq_of_ne_one G X h2 T b a hb ha1).trans ha⟩

theorem isMulCommutative_of_simple
    (G X : Type*) [Group G] [MulAction G X] [Nonempty X]
    (h2 : MulAction.IsMultiplyPretransitive G X 2)
    (T : Subgroup G) [T.Normal] [IsCancelSMul T X] [Finite T] [IsSimpleGroup T] :
    IsMulCommutative T := by
  obtain ⟨p, hp, hT⟩ := exists_prime_isPGroup G X h2 T
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Group.IsNilpotent T := hT.isNilpotent
  exact IsMulCommutative.of_comm (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance)

end FiveTransitive.SemiregularNormalTwo

end CFSG
