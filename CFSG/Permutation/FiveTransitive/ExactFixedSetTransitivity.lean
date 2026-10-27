module

public import CFSG.Permutation.FiveTransitive.ExactFourFixedSetTransitivity
public import CFSG.Permutation.FiveTransitive.OneFixerSuccessorTransitivity

public section

namespace CFSG

namespace FiveTransitive.ExactFixedSetTransitivity

open MulAction SubMulAction

theorem all_fixers_down
    {G X : Type*} [Group G] [MulAction G X] [Finite X] (k : ℕ)
    (hsize : k + 2 ≤ Nat.card X)
    (hfix : ∀ s : Set X, s.ncard = k →
      IsPretransitive (fixingSubgroup G s) (ofFixingSubgroup G s)) :
    ∀ j : ℕ, j ≤ k → ∀ s : Set X, s.ncard = j →
      IsPretransitive (fixingSubgroup G s) (ofFixingSubgroup G s) := by
  induction k with
  | zero =>
    intro j hj
    have heq : j = 0 := by omega
    subst j
    exact hfix
  | succ k ih =>
    have hk := ExactFourFixedSetTransitivity.all_fixers_step_down (G := G) k hsize hfix
    intro j hj
    by_cases heq : j = k + 1
    · subst j
      exact hfix
    · exact ih (by omega) hk j (by omega)

theorem multiply_of_all_fixers
    {G X : Type*} [Group G] [MulAction G X] [Finite X] (k : ℕ)
    (hsize : k ≤ Nat.card X)
    (hfix : ∀ j : ℕ, j < k → ∀ s : Set X, s.ncard = j →
      IsPretransitive (fixingSubgroup G s) (ofFixingSubgroup G s)) :
    IsMultiplyPretransitive G X k := by
  classical
  induction k with
  | zero => exact is_zero_pretransitive'
  | succ k ih =>
    have hk : IsMultiplyPretransitive G X k := ih (by omega)
      (fun j hj => hfix j (by omega))
    let _ : Fintype X := Fintype.ofFinite X
    obtain ⟨e⟩ : Nonempty (Fin k ↪ X) := Function.Embedding.nonempty_of_card_le (by
      simpa only [Fintype.card_fin, Nat.card_eq_fintype_card] using (show k ≤ Nat.card X by omega))
    have hc : (Set.range e).ncard = k := by
      rw [Set.ncard_range_of_injective e.injective, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact OneFixerSuccessorTransitivity.succ_of_one_transitive_fixing G X k hk e
      (hfix k (by omega) _ hc)

private theorem predecessor_fixer_pretransitive
    {G X : Type*} [Group G] [MulAction G X] [Finite X] (k : ℕ)
    (hbase : ∀ s : Set X, s.ncard = k + 1 →
      ∃ Q : Subgroup G, IsPGroup 2 Q ∧ fixedPoints Q X = s)
    (s : Set X) (hs : s.ncard = k) :
    IsPretransitive (fixingSubgroup G s) (ofFixingSubgroup G s) := by
  classical
  let H := fixingSubgroup G s
  apply UniqueTwoFixedPointTransitivity.isPretransitive_of_unique_fixed_point
  intro x
  obtain ⟨Q, hQ, hQfix⟩ := hbase (insert x.val s) (by
    rw [Set.ncard_insert_of_notMem x.property, hs])
  have hQH : Q ≤ H := by
    intro q hq
    rw [mem_fixingSubgroup_iff]
    intro y hy
    have hyfix : y ∈ fixedPoints Q X := by
      rw [hQfix]
      exact Set.mem_insert_of_mem x.val hy
    exact mem_fixedPoints.mp hyfix ⟨q, hq⟩
  let R : Subgroup H := Q.subgroupOf H
  let e : R ≃* Q := Subgroup.subgroupOfEquivOfLe hQH
  have hR : IsPGroup 2 R := hQ.of_injective e.toMonoidHom e.injective
  refine ⟨R, hR, ?_⟩
  ext y
  rw [Set.mem_singleton_iff]
  constructor
  · intro hy
    have hyQ : y.val ∈ fixedPoints Q X := by
      intro q
      exact congrArg Subtype.val (mem_fixedPoints.mp hy
        (⟨⟨q.val, hQH q.property⟩, q.property⟩ : R))
    rw [hQfix, Set.mem_insert_iff] at hyQ
    rcases hyQ with heq | hys
    · exact Subtype.ext heq
    · exact (y.property hys).elim
  · intro hy
    subst y
    intro r
    apply Subtype.ext
    have hx : x.val ∈ fixedPoints Q X := by rw [hQfix]; exact Set.mem_insert _ _
    exact mem_fixedPoints.mp hx ⟨r.val.val, r.property⟩

theorem multiply_of_exact_two_subgroup_fixed_sets
    {G X : Type*} [Group G] [MulAction G X] [Finite X] (k : ℕ)
    (hsize : k + 1 ≤ Nat.card X)
    (hbase : ∀ s : Set X, s.ncard = k →
      ∃ Q : Subgroup G, IsPGroup 2 Q ∧ fixedPoints Q X = s) :
    IsMultiplyPretransitive G X k := by
  cases k with
  | zero => exact is_zero_pretransitive'
  | succ k =>
    have hfix := predecessor_fixer_pretransitive (G := G) k hbase
    have hall := all_fixers_down k hsize hfix
    exact multiply_of_all_fixers (k + 1) (by omega) (fun j hj => hall j (by omega))

end FiveTransitive.ExactFixedSetTransitivity

end CFSG
