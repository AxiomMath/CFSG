module

public import CFSG.Permutation.FiveTransitive.NormalInheritsTwo

public section

namespace CFSG

namespace FiveTransitive.NormalInheritsThree

private theorem exists_ne_one_fixed_of_four
    (G X : Type*) [Group G] [Fintype X] [MulAction G X]
    (hcard : 5 ≤ Fintype.card X)
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (N : Subgroup G) [N.Normal] [MulAction.IsPretransitive N X] :
    ∃ (a : N) (x : X), a ≠ 1 ∧ a • x = x := by
  by_contra h
  have hfree : ∀ (a : N) (x : X), a • x = x → a = 1 := by
    intro a x hax
    by_contra ha
    exact h ⟨a, x, ha, hax⟩
  let _ : IsCancelSMul N X := isCancelSMul_iff_eq_one_of_smul_eq.mpr hfree
  exact AbelianNormalObstruction.false_of_regular_normal_subgroup G X hcard h4 N

theorem two_of_four
    (G X : Type*) [Group G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcard : 5 ≤ Fintype.card X)
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (N : Subgroup G) [N.Normal] [Nontrivial N] :
    MulAction.IsMultiplyPretransitive N X 2 := by
  let _ : MulAction.IsMultiplyPretransitive G X 4 := h4
  have h3 : MulAction.IsMultiplyPretransitive G X 3 :=
    MulAction.isMultiplyPretransitive_of_le (G := G) (α := X) (m := 3) (n := 4)
      (by omega) (by simpa only [Nat.card_eq_fintype_card] using (show 4 ≤ Fintype.card X by omega))
  have h2 : MulAction.IsMultiplyPretransitive G X 2 :=
    MulAction.isMultiplyPretransitive_of_le (G := G) (α := X) (m := 2) (n := 4)
      (by omega) (by simpa only [Nat.card_eq_fintype_card] using (show 4 ≤ Fintype.card X by omega))
  let _ : MulAction.IsMultiplyPretransitive G X 2 := h2
  let _ : MulAction.IsPretransitive G X := MulAction.isPretransitive_of_is_two_pretransitive
  let _ : MulAction.IsPreprimitive G X := MulAction.isPreprimitive_of_is_two_pretransitive h2
  let _ : MulAction.IsPretransitive N X :=
    NormalSubgroupStructure.isPretransitive_of_nontrivial_normal G X N
  obtain ⟨a, x, ha, hax⟩ := exists_ne_one_fixed_of_four G X hcard h4 N
  exact NormalInheritsTwo.isMultiplyPretransitive_two_of_fixed G X h3 N a x ha hax

private theorem faithfulSMul_ofStabilizer
    (G X : Type*) [Group G] [MulAction G X] [FaithfulSMul G X] (x : X) :
    FaithfulSMul (MulAction.stabilizer G x) (SubMulAction.ofStabilizer G x) := by
  constructor
  intro a b hab
  apply Subtype.ext
  apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
  intro y
  by_cases hy : y = x
  · subst y
    exact a.property.trans b.property.symm
  · exact congrArg Subtype.val (hab ⟨y, hy⟩)

theorem three_of_five
    (G X : Type*) [Group G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcard : 6 ≤ Fintype.card X)
    (h5 : MulAction.IsMultiplyPretransitive G X 5)
    (N : Subgroup G) [N.Normal] [Nontrivial N] :
    MulAction.IsMultiplyPretransitive N X 3 := by
  classical
  let _ : MulAction.IsMultiplyPretransitive G X 5 := h5
  have h4 : MulAction.IsMultiplyPretransitive G X 4 :=
    MulAction.isMultiplyPretransitive_of_le (G := G) (α := X) (m := 4) (n := 5)
      (by omega) (by simpa only [Nat.card_eq_fintype_card] using (show 5 ≤ Fintype.card X by omega))
  have h2 : MulAction.IsMultiplyPretransitive G X 2 :=
    MulAction.isMultiplyPretransitive_of_le (G := G) (α := X) (m := 2) (n := 5)
      (by omega) (by simpa only [Nat.card_eq_fintype_card] using (show 5 ≤ Fintype.card X by omega))
  let _ : MulAction.IsMultiplyPretransitive G X 2 := h2
  let _ : MulAction.IsPretransitive G X := MulAction.isPretransitive_of_is_two_pretransitive
  let _ : MulAction.IsPreprimitive G X := MulAction.isPreprimitive_of_is_two_pretransitive h2
  let _ : MulAction.IsPretransitive N X :=
    NormalSubgroupStructure.isPretransitive_of_nontrivial_normal G X N
  obtain ⟨a, x, ha, hax⟩ := exists_ne_one_fixed_of_four G X (by omega) h4 N
  let K : Subgroup G := MulAction.stabilizer G x
  let H : Subgroup K := N.comap K.subtype
  let Y := SubMulAction.ofStabilizer G x
  let _ : Fintype Y := Fintype.ofFinite Y
  let _ : FaithfulSMul K Y := faithfulSMul_ofStabilizer G X x
  have hK4 : MulAction.IsMultiplyPretransitive K Y 4 :=
    (SubMulAction.ofStabilizer.isMultiplyPretransitive (G := G) (α := X)
      (a := x) (n := 4)).mp h5
  have hYcard : 5 ≤ Fintype.card Y := by
    have h := SubMulAction.nat_card_ofStabilizer_add_one_eq G x
    change Nat.card Y + 1 = Nat.card X at h
    simp only [Nat.card_eq_fintype_card] at h
    omega
  let aH : H := ⟨⟨(a : G), hax⟩, a.property⟩
  let _ : Nontrivial H := by
    refine ⟨⟨aH, 1, ?_⟩⟩
    intro h
    apply ha
    apply Subtype.ext
    exact congrArg (fun z : H => ((z : K) : G)) h
  have hH2 := two_of_four K Y hYcard hK4 H
  have hNstab : MulAction.IsMultiplyPretransitive (MulAction.stabilizer N x)
      (SubMulAction.ofStabilizer N x) 2 := by
    rw [MulAction.isMultiplyPretransitive_iff] at hH2 ⊢
    intro y z
    obtain ⟨h, hh⟩ := hH2 y z
    let n : N := ⟨((h : K) : G), h.property⟩
    have hnx : n • x = x := (h : K).property
    refine ⟨⟨n, hnx⟩, ?_⟩
    ext i
    exact congrArg Subtype.val (DFunLike.congr_fun hh i)
  exact (SubMulAction.ofStabilizer.isMultiplyPretransitive (G := N) (α := X)
    (a := x) (n := 2)).mpr hNstab

end FiveTransitive.NormalInheritsThree

end CFSG
