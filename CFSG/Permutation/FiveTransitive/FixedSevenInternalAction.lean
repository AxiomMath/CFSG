module

public import CFSG.Permutation.FiveTransitive.NormalSylowFixedOrderPairs
public import CFSG.Permutation.FiveTransitive.BaseSylowConjugacy

public section

namespace CFSG

namespace FiveTransitive.FixedSevenInternalAction

open MulAction GenericSylowFixedAction

theorem image_eq_alternating
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h5 : IsMultiplyPretransitive G X 5)
    (N : Subgroup G) [N.Normal] (hN4 : IsMultiplyPretransitive N X 4)
    (s : Set X) (hs : s.ncard = 4) (S : Sylow 2 (fixingSubgroup N s))
    (hseven : Nat.card (sylowFixedPoints N X s S) = 7) :
    let F := sylowFixedPoints N X s S
    letI := Fintype.ofFinite F
    letI := Classical.decEq F
    (toPermHom (sylowNormalizer N X s S) F).range = alternatingGroup F := by
  classical
  intro F
  let _ := Fintype.ofFinite F
  let _ := Classical.decEq F
  let L := (toPermHom (sylowNormalizer N X s S) F).range
  have hL : Nat.card L = 2520 := by
    have h := NormalSylowFixedOrderPairs.degree_order_pairs G X h5 N hN4 s hs S
    change (Nat.card F = 4 ∧ Nat.card L = 24) ∨
      (Nat.card F = 5 ∧ Nat.card L = 120) ∨
      (Nat.card F = 6 ∧ Nat.card L = 360) ∨
      (Nat.card F = 7 ∧ Nat.card L = 2520) at h
    change Nat.card F = 7 at hseven
    omega
  apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
  change L.index = 2
  have h := L.index_mul_card
  rw [hL, Nat.card_perm, hseven] at h
  norm_num [Nat.factorial] at h
  omega

private theorem normalizer_five_transitive
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h5 : IsMultiplyPretransitive G X 5)
    (N : Subgroup G) [N.Normal] (hN4 : IsMultiplyPretransitive N X 4)
    (s : Set X) (hs : s.ncard = 4) (S : Sylow 2 (fixingSubgroup N s))
    (hseven : Nat.card (sylowFixedPoints N X s S) = 7) :
    IsMultiplyPretransitive (sylowNormalizer N X s S) (sylowFixedPoints N X s S) 5 := by
  classical
  let F := sylowFixedPoints N X s S
  let _ := Fintype.ofFinite F
  let _ := Classical.decEq F
  let L := (toPermHom (sylowNormalizer N X s S) F).range
  have hL5 : IsMultiplyPretransitive L F 5 := by
    rw [show L = alternatingGroup F from image_eq_alternating G X h5 N hN4 s hs S hseven]
    have h := alternatingGroup.isMultiplyPretransitive F
    rwa [show Nat.card F = 7 from hseven] at h
  rw [isMultiplyPretransitive_iff]
  intro a b
  obtain ⟨g, hg⟩ := hL5.exists_smul_eq a b
  obtain ⟨c, hc⟩ := g.property
  refine ⟨c, ?_⟩
  apply Function.Embedding.ext
  intro i
  have hi := DFunLike.congr_fun hg i
  change (g.val : Equiv.Perm F) (a i) = b i at hi
  rw [← hc] at hi
  exact hi

private theorem connect_fixed_complement_of_normalizer_five
    (H X : Type) [Group H] [Finite H] [Fintype X] [MulAction H X]
    (s : Set X) (hs : s.ncard = 4) (S : Sylow 2 (fixingSubgroup H s))
    (hfive : IsMultiplyPretransitive (sylowNormalizer H X s S) (sylowFixedPoints H X s S) 5)
    (u v : X) (hu : u ∉ s) (hv : v ∉ s)
    (hufix : ∀ q : S, q • u = u) (hvfix : ∀ q : S, q • v = v) :
    ∃ n : fixingSubgroup H s, n • u = v := by
  let F := sylowFixedPoints H X s S
  have hbase : s ⊆ (F : Set X) := base_subset_fixedPoints H X s S
  obtain ⟨e, he⟩ := BaseSylowConjugacy.exists_embedding_range X 4 s hs
  let eF : Fin 4 ↪ F :=
    { toFun := fun i => ⟨e i, hbase (by rw [← he]; exact ⟨i, rfl⟩)⟩
      inj' := fun i j h => e.injective (congrArg Subtype.val h) }
  let uF : F := ⟨u, (NormalSylowFixedDegree.mem_internal_fixedPoints_iff H X s S u).mpr hufix⟩
  let vF : F := ⟨v, (NormalSylowFixedDegree.mem_internal_fixedPoints_iff H X s S v).mpr hvfix⟩
  have hunot : uF ∉ Set.range eF := by
    rintro ⟨i, hi⟩
    apply hu
    rw [← he]
    exact ⟨i, congrArg Subtype.val hi⟩
  have hvnot : vF ∉ Set.range eF := by
    rintro ⟨i, hi⟩
    apply hv
    rw [← he]
    exact ⟨i, congrArg Subtype.val hi⟩
  obtain ⟨c, hc⟩ := hfive.exists_smul_eq (Fin.Embedding.snoc eF hunot) (Fin.Embedding.snoc eF hvnot)
  have hcfirst (i : Fin 4) : c • eF i = eF i := by
    have hi := DFunLike.congr_fun hc i.castSucc
    change c • (Fin.Embedding.snoc eF hunot) i.castSucc =
      (Fin.Embedding.snoc eF hvnot) i.castSucc at hi
    simpa only [Fin.Embedding.coe_snoc, Fin.snoc_castSucc] using hi
  have hclast : c • uF = vF := by
    have hi := DFunLike.congr_fun hc (Fin.last 4)
    change c • (Fin.Embedding.snoc eF hunot) (Fin.last 4) =
      (Fin.Embedding.snoc eF hvnot) (Fin.last 4) at hi
    simpa only [Fin.Embedding.coe_snoc, Fin.snoc_last] using hi
  have hcfix : (c : H) ∈ fixingSubgroup H s := by
    rw [mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨i, rfl⟩ : x ∈ Set.range e := by rwa [he]
    exact congrArg Subtype.val (hcfirst i)
  exact ⟨⟨c, hcfix⟩, congrArg Subtype.val hclast⟩

theorem connect_fixed_complement
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h5 : IsMultiplyPretransitive G X 5)
    (N : Subgroup G) [N.Normal] (hN4 : IsMultiplyPretransitive N X 4)
    (s : Set X) (hs : s.ncard = 4) (S : Sylow 2 (fixingSubgroup N s))
    (hseven : Nat.card (sylowFixedPoints N X s S) = 7)
    (u v : X) (hu : u ∉ s) (hv : v ∉ s)
    (hufix : ∀ q : S, q • u = u) (hvfix : ∀ q : S, q • v = v) :
    ∃ n : fixingSubgroup N s, n • u = v :=
  connect_fixed_complement_of_normalizer_five N X s hs S
    (normalizer_five_transitive G X h5 N hN4 s hs S hseven) u v hu hv hufix hvfix

end FiveTransitive.FixedSevenInternalAction

end CFSG
