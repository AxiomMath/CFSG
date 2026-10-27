module

public import CFSG.Permutation.FiveTransitive.NormalSubgroupStructure

public section

namespace CFSG

namespace FiveTransitive.NormalInheritsTwo

theorem isMultiplyPretransitive_two_of_fixed
    (G X : Type*) [Group G] [MulAction G X] [FaithfulSMul G X]
    [MulAction.IsPretransitive G X]
    (h3 : MulAction.IsMultiplyPretransitive G X 3)
    (N : Subgroup G) [N.Normal] [MulAction.IsPretransitive N X]
    (a : N) (x : X) (ha : a ≠ 1) (hax : a • x = x) :
    MulAction.IsMultiplyPretransitive N X 2 := by
  let K : Subgroup G := MulAction.stabilizer G x
  let H : Subgroup K := N.comap K.subtype
  let Y := SubMulAction.ofStabilizer G x
  have hK2 : MulAction.IsMultiplyPretransitive K Y 2 :=
    (SubMulAction.ofStabilizer.isMultiplyPretransitive (G := G) (α := X)
      (a := x) (n := 2)).mp h3
  let _ : MulAction.IsPreprimitive K Y :=
    MulAction.isPreprimitive_of_is_two_pretransitive hK2
  let aH : H := ⟨⟨(a : G), hax⟩, a.property⟩
  have hHtrans : MulAction.IsPretransitive H Y := by
    apply MulAction.IsQuasiPreprimitive.isPretransitive_of_normal
    intro hfixed
    apply ha
    apply Subtype.ext
    apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
    intro y
    change (a : G) • y = (1 : G) • y
    by_cases hy : y = x
    · subst y
      simpa only [one_smul, Subgroup.smul_def] using hax
    · have hyfixed : (⟨y, hy⟩ : Y) ∈ MulAction.fixedPoints H Y := by
        rw [hfixed]
        exact Set.mem_univ _
      have hyact := (MulAction.mem_fixedPoints.mp hyfixed) aH
      simpa only [one_smul, Subgroup.smul_def, SubMulAction.val_smul, aH] using
        congrArg Subtype.val hyact
  have hNstab : MulAction.IsPretransitive (MulAction.stabilizer N x)
      (SubMulAction.ofStabilizer N x) := by
    constructor
    intro y z
    obtain ⟨h, hh⟩ := hHtrans.exists_smul_eq (⟨y, y.property⟩ : Y) (⟨z, z.property⟩ : Y)
    let n : N := ⟨((h : K) : G), h.property⟩
    have hnx : n • x = x := (h : K).property
    refine ⟨⟨n, hnx⟩, ?_⟩
    apply Subtype.ext
    exact congrArg Subtype.val hh
  exact (SubMulAction.ofStabilizer.isMultiplyPretransitive (G := N) (α := X)
    (a := x) (n := 1)).mpr (MulAction.is_one_pretransitive_iff.mpr hNstab)

theorem isMultiplyPretransitive_two_of_five_transitive_normal
    (G X : Type*) [Group G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : 5 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i)
    (N : Subgroup G) [N.Normal] [Nontrivial N] :
    MulAction.IsMultiplyPretransitive N X 2 := by
  have h5G : MulAction.IsMultiplyPretransitive G X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
    exact ⟨g, Function.Embedding.ext hg⟩
  let _ : MulAction.IsMultiplyPretransitive G X 5 := h5G
  have h3 : MulAction.IsMultiplyPretransitive G X 3 :=
    MulAction.isMultiplyPretransitive_of_le (G := G) (α := X) (m := 3) (n := 5)
      (by omega) (by simpa only [Nat.card_eq_fintype_card] using hcard)
  have h2 : MulAction.IsMultiplyPretransitive G X 2 :=
    MulAction.isMultiplyPretransitive_of_le (G := G) (α := X) (m := 2) (n := 5)
      (by omega) (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let _ : MulAction.IsMultiplyPretransitive G X 2 := h2
  let _ : MulAction.IsPretransitive G X :=
    MulAction.isPretransitive_of_is_two_pretransitive
  let _ : MulAction.IsPreprimitive G X :=
    MulAction.isPreprimitive_of_is_two_pretransitive h2
  let _ : MulAction.IsPretransitive N X :=
    NormalSubgroupStructure.isPretransitive_of_nontrivial_normal G X N
  by_contra hNtwo
  have hfree : ∀ (a : N) (x : X), a • x = x → a = 1 := by
    intro a x hax
    by_contra ha
    exact hNtwo (isMultiplyPretransitive_two_of_fixed G X h3 N a x ha hax)
  let _ : IsCancelSMul N X := isCancelSMul_iff_eq_one_of_smul_eq.mpr hfree
  exact AbelianNormalObstruction.false_of_regular_normal_of_five_transitive
    G X hcard h5 N

end FiveTransitive.NormalInheritsTwo

end CFSG
