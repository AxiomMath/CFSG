module

public import CFSG.Permutation.FiveTransitive.ExactFixedSetTransitivity
public import CFSG.Permutation.FiveTransitive.BaseSylowConjugacy
public import CFSG.Permutation.FiveTransitive.OyamaMinimalOrbitDescent

public section

namespace CFSG

namespace FiveTransitive.Degree60FiveFixedCriterion

open MulAction SubMulAction UniqueTwoFixedPointTransitivity OyamaMinimalOrbitDescent

private theorem isPretransitive_of_unique_fixed_point
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hpoint : ∀ x : X, ∃ P : Subgroup G, IsPGroup 5 P ∧ fixedPoints P X = {x}) :
    IsPretransitive G X := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  constructor
  intro x y
  suffices hy : y ∈ orbit G x by exact mem_orbit_iff.mp hy
  by_contra hy
  obtain ⟨P, hP, hPx⟩ := hpoint x
  obtain ⟨Q, hQ, hQy⟩ := hpoint y
  have hp := hP.card_modEq_card_fixedPoints (orbitAction P x)
  have hq := hQ.card_modEq_card_fixedPoints (orbitAction Q x)
  change Nat.card (orbit G x) % 5 = Nat.card (fixedPoints P (orbitAction P x)) % 5 at hp
  change Nat.card (orbit G x) % 5 = Nat.card (fixedPoints Q (orbitAction Q x)) % 5 at hq
  rw [card_fixed_orbit P x x hPx, ite_eq_left (mem_orbit_self x)] at hp
  rw [card_fixed_orbit Q x y hQy, ite_eq_right hy] at hq
  omega

private theorem predecessor_fixer_pretransitive
    {G X : Type*} [Group G] [MulAction G X] [Finite X] (k : ℕ)
    (hbase : ∀ s : Set X, s.ncard = k + 1 →
      ∃ Q : Subgroup G, IsPGroup 5 Q ∧ fixedPoints Q X = s)
    (s : Set X) (hs : s.ncard = k) :
    IsPretransitive (fixingSubgroup G s) (ofFixingSubgroup G s) := by
  classical
  let H := fixingSubgroup G s
  apply isPretransitive_of_unique_fixed_point
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
  have hR : IsPGroup 5 R := hQ.of_injective e.toMonoidHom e.injective
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

private theorem multiply_of_exact_five_subgroup_fixed_sets
    {G X : Type*} [Group G] [MulAction G X] [Finite X] (k : ℕ)
    (hsize : k + 1 ≤ Nat.card X)
    (hbase : ∀ s : Set X, s.ncard = k →
      ∃ Q : Subgroup G, IsPGroup 5 Q ∧ fixedPoints Q X = s) :
    IsMultiplyPretransitive G X k := by
  cases k with
  | zero => exact is_zero_pretransitive'
  | succ k =>
    have hfix := predecessor_fixer_pretransitive (G := G) k hbase
    have hall := ExactFixedSetTransitivity.all_fixers_down k hsize hfix
    exact ExactFixedSetTransitivity.multiply_of_all_fixers (k + 1) (by omega) (fun j hj => hall j (by omega))

theorem range_subset_fixed
    {G X : Type*} [Group G] [MulAction G X] {k : ℕ} (a : Fin k ↪ X)
    (S : Sylow 5 (stabilizer G a)) :
    Set.range a ⊆ fixedPoints (ambientSylow a S) X := by
  rintro _ ⟨i, rfl⟩
  intro q
  obtain ⟨u, hu, he⟩ := Subgroup.mem_map.mp q.property
  have hf : u.val • a i = a i := DFunLike.congr_fun u.property i
  change q.val • a i = a i
  rw [← he]
  exact hf

theorem multiply_of_tuple_sylow_fixed_card
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    (k : ℕ) (hsize : k + 1 ≤ Nat.card X)
    (hlocal : ∀ a : Fin k ↪ X, ∃ S : Sylow 5 (stabilizer G a),
      Nat.card (fixedPoints (ambientSylow a S) X) = k) :
    IsMultiplyPretransitive G X k := by
  classical
  let _ : Fintype X := Fintype.ofFinite X
  apply multiply_of_exact_five_subgroup_fixed_sets k hsize
  intro s hs
  obtain ⟨a, ha⟩ := BaseSylowConjugacy.exists_embedding_range X k s hs
  obtain ⟨S, hS⟩ := hlocal a
  refine ⟨ambientSylow a S, S.isPGroup'.map (stabilizer G a).subtype, ?_⟩
  have hsub : s ⊆ fixedPoints (ambientSylow a S) X := by
    rw [← ha]
    exact range_subset_fixed a S
  apply (Set.eq_of_subset_of_ncard_le hsub ?_).symm
  rw [← Nat.card_coe_set_eq, hS, hs]

end FiveTransitive.Degree60FiveFixedCriterion

end CFSG
