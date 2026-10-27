module

public import CFSG.Permutation.FiveTransitive.NormalInheritsThree

public section

namespace CFSG

namespace FiveTransitive.NormalFourOrSharpThree

private theorem faithfulSMul_ofFixingSubgroup
    (G X : Type*) [Group G] [MulAction G X] [FaithfulSMul G X] (s : Set X) :
    FaithfulSMul (fixingSubgroup G s) (SubMulAction.ofFixingSubgroup G s) := by
  constructor
  intro a b hab
  apply Subtype.ext
  apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
  intro x
  by_cases hx : x ∈ s
  · exact ((mem_fixingSubgroup_iff G).mp a.property x hx).trans
      ((mem_fixingSubgroup_iff G).mp b.property x hx).symm
  · exact congrArg Subtype.val (hab ⟨x, hx⟩)

theorem isPretransitive_fixing_normal
    (G X : Type*) [Group G] [MulAction G X] [FaithfulSMul G X]
    (N : Subgroup G) [N.Normal] (s : Set X)
    (h2 : MulAction.IsMultiplyPretransitive (fixingSubgroup G s)
      (SubMulAction.ofFixingSubgroup G s) 2)
    [Nontrivial (fixingSubgroup N s)] :
    MulAction.IsPretransitive (fixingSubgroup N s)
      (SubMulAction.ofFixingSubgroup N s) := by
  let K := fixingSubgroup G s
  let H : Subgroup K := N.comap K.subtype
  let Y := SubMulAction.ofFixingSubgroup G s
  let _ : FaithfulSMul K Y := faithfulSMul_ofFixingSubgroup G X s
  let _ : MulAction.IsPreprimitive K Y := MulAction.isPreprimitive_of_is_two_pretransitive h2
  obtain ⟨a, ha⟩ := exists_ne (1 : fixingSubgroup N s)
  let aH : H := ⟨⟨((a : N) : G), by
      intro x
      exact (mem_fixingSubgroup_iff N).mp a.property x x.property⟩, (a : N).property⟩
  let _ : Nontrivial H := by
    refine ⟨⟨aH, 1, ?_⟩⟩
    intro h
    apply ha
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : H => ((z : K) : G)) h
  have hHtrans : MulAction.IsPretransitive H Y :=
    NormalSubgroupStructure.isPretransitive_of_nontrivial_normal K Y H
  constructor
  intro y z
  obtain ⟨h, hh⟩ := hHtrans.exists_smul_eq y z
  let n : N := ⟨((h : K) : G), h.property⟩
  refine ⟨⟨n, ?_⟩, ?_⟩
  · intro x
    exact (mem_fixingSubgroup_iff G).mp (h : K).property x x.property
  · exact hh

private theorem card_eq_descFactorial_of_fixing_subsingleton
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (k : ℕ) (hk : MulAction.IsMultiplyPretransitive G X k)
    (s : Set X) (hs : s.ncard = k) [Subsingleton (fixingSubgroup G s)] :
    Nat.card G = (Fintype.card X).descFactorial k := by
  have hks : MulAction.IsMultiplyPretransitive G X s.ncard := by simpa only [hs] using hk
  have hindex := hks.index_of_fixingSubgroup_eq s
  rw [hs, Nat.card_eq_fintype_card] at hindex
  have hfixcard : Nat.card (fixingSubgroup G s) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  have hmul := (fixingSubgroup G s).index_mul_card
  rw [hindex, hfixcard, mul_one] at hmul
  rw [← hmul, Nat.descFactorial_eq_factorial_mul_choose, Nat.mul_comm]

theorem succ_of_transitive_fixing
    (G X : Type*) [Group G] [MulAction G X] (k : ℕ)
    (hk : MulAction.IsMultiplyPretransitive G X k)
    (hfix : ∀ s : Set X, s.ncard = k →
      MulAction.IsPretransitive (fixingSubgroup G s)
        (SubMulAction.ofFixingSubgroup G s)) :
    MulAction.IsMultiplyPretransitive G X (k + 1) := by
  rw [MulAction.isMultiplyPretransitive_iff] at hk ⊢
  intro a b
  let a0 : Fin k ↪ X := ⟨fun i => a i.castSucc, a.injective.comp (Fin.castSucc_injective k)⟩
  let b0 : Fin k ↪ X := ⟨fun i => b i.castSucc, b.injective.comp (Fin.castSucc_injective k)⟩
  obtain ⟨g, hg⟩ := hk a0 b0
  let s : Set X := Set.range b0
  have hs : s.ncard = k := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective b0.injective
  have hgfirst (i : Fin k) : g • a i.castSucc = b i.castSucc :=
    DFunLike.congr_fun hg i
  have hlast : b (Fin.last k) ∉ s := by
    rintro ⟨i, hi⟩
    have := b.injective hi
    exact Fin.castSucc_ne_last i this
  have hglast : g • a (Fin.last k) ∉ s := by
    rintro ⟨i, hi⟩
    have h := (hgfirst i).trans hi
    have heq := a.injective (smul_left_cancel g h)
    exact Fin.castSucc_ne_last i heq
  obtain ⟨h, hh⟩ := (hfix s hs).exists_smul_eq
    (⟨g • a (Fin.last k), hglast⟩ : SubMulAction.ofFixingSubgroup G s)
    (⟨b (Fin.last k), hlast⟩ : SubMulAction.ofFixingSubgroup G s)
  refine ⟨(h : G) * g, ?_⟩
  ext i
  change ((h : G) * g) • a i = b i
  rw [mul_smul]
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [hgfirst j]
    exact (mem_fixingSubgroup_iff G).mp h.property _ ⟨j, rfl⟩
  · exact congrArg Subtype.val hh

theorem four_or_card_eq_three_descFactorial
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcard : 6 ≤ Fintype.card X)
    (h5 : MulAction.IsMultiplyPretransitive G X 5)
    (N : Subgroup G) [N.Normal] [Nontrivial N] :
    MulAction.IsMultiplyPretransitive N X 4 ∨
      Nat.card N = (Fintype.card X).descFactorial 3 := by
  classical
  have hN3 := NormalInheritsThree.three_of_five G X hcard h5 N
  by_cases hNcard : Nat.card N = (Fintype.card X).descFactorial 3
  · exact Or.inr hNcard
  left
  apply succ_of_transitive_fixing N X 3 hN3
  intro s hs
  let _ : Nontrivial (fixingSubgroup N s) := by
    by_contra h
    let _ : Subsingleton (fixingSubgroup N s) := not_nontrivial_iff_subsingleton.mp h
    exact hNcard (card_eq_descFactorial_of_fixing_subsingleton N X 3 hN3 s hs)
  let _ : MulAction.IsMultiplyPretransitive G X 5 := h5
  apply isPretransitive_fixing_normal G X N s
  exact SubMulAction.ofFixingSubgroup.isMultiplyPretransitive G (m := 2) (n := 5) s (by omega)

end FiveTransitive.NormalFourOrSharpThree

end CFSG
