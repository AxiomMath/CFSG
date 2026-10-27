module

public import CFSG.Permutation.FiveTransitive.Degree54TwoSmallKernelCount
public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport

public section

namespace CFSG

namespace FiveTransitive.Degree54TwoSmallKernelBound
open MulAction

theorem card_le_eight
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 2 Q) (hfixed : Nat.card (fixedPoints Q X) = 6)
    (x : X) (hO : Nat.card (orbit Q x) = 16)
    (hsmall : ∀ y : X, y ∉ orbit Q x → Nat.card (orbit Q y) ≤ 4) :
    Nat.card (toPermHom Q (orbit Q x)).ker ≤ 8 := by
  classical
  let O := orbit Q x
  let f := toPermHom Q O
  let K := f.ker
  let s := (fixedPoints Q X ∪ O).toFinset
  have hdis : Disjoint (fixedPoints Q X) O := by
    apply Set.disjoint_left.mpr
    intro y hy hyO
    have he : orbit Q y = O := orbit_eq_iff.mpr hyO
    have h1 : Nat.card (orbit Q y) = 1 := by
      rw [Nat.card_eq_fintype_card]
      exact mem_fixedPoints_iff_card_orbit_eq_one.mp hy
    rw [he,hO] at h1
    omega
  have hs : s.card = 22 := by
    rw [Set.toFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq,
      Set.ncard_union_eq hdis,← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,hfixed,hO]
  have hfixO : ∀ k : K, ∀ y ∈ O, k • y = y := by
    intro k y hy
    have he : f k.val = 1 := k.property
    exact congrArg Subtype.val (DFunLike.congr_fun he (⟨y,hy⟩ : O))
  have hfixs : ∀ k : K, ∀ y ∈ s, k • y = y := by
    intro k y hy
    rcases Set.mem_toFinset.mp hy with hy | hy
    · exact hy k.val
    · exact hfixO k y hy
  have horbit : ∀ y : X, Nat.card (orbit K y) ≤ 4 := by
    intro y
    by_cases hy : y ∈ O
    · have he : orbit K y = {y} := by
        ext z
        constructor
        · rintro ⟨k,rfl⟩
          exact hfixO k y hy
        · rintro rfl
          exact mem_orbit_self _
      rw [he,Nat.card_coe_set_eq,Set.ncard_singleton]
      omega
    · have hsub : orbit K y ⊆ orbit Q y := by
        rintro z ⟨k,rfl⟩
        exact ⟨k.val,rfl⟩
      have hb : Nat.card (orbit K y) ≤ Nat.card (orbit Q y) := by
        rw [Nat.card_coe_set_eq,Nat.card_coe_set_eq]
        exact Set.ncard_le_ncard hsub
      exact hb.trans (hsmall y hy)
  have hbound : ∀ k : K, k ≠ 1 → Nat.card (fixedBy X k) ≤ 27 := by
    intro k hk
    have hne : k.val.val.val ≠ 1 := by
      intro he
      exact hk (Subtype.ext (Subtype.ext (Subtype.ext he)))
    have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5 hnotAlt
      k.val.val.property hne
    rw [hcard] at hb
    change Nat.card (Function.fixedPoints k.val.val.val) ≤ 27
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,k.val.val.val.sum_cycleType,hcard]
    omega
  have hb := Degree54TwoSmallKernelCount.card_le_nine hcard s hs hfixs horbit hbound
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp (hQ.to_subgroup K)
  have he3 : e ≤ 3 := by
    by_contra hn
    have hp : 16 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 4 ≤ e)
    rw [he] at hb
    omega
  rw [he]
  exact Nat.pow_le_pow_right (by decide) he3

end FiveTransitive.Degree54TwoSmallKernelBound

end CFSG
