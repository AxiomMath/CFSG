module

public import CFSG.Permutation.FiveTransitive.SetwiseSylowNormalizer
public import CFSG.Permutation.FiveTransitive.OyamaMinimalOrbitChoice

public section

namespace CFSG

namespace FiveTransitive.OyamaTripleSylow

open MulAction

variable {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]

abbrev image (s : Set X) (S : Sylow 2 (fixingSubgroup G s)) : Subgroup G :=
  (S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype

@[expose] def FourFixedSix (G X : Type*) [Group G] [MulAction G X] : Prop :=
  ∀ (s : Set X), s.ncard = 4 → ∀ S : Sylow 2 (fixingSubgroup G s),
    (fixedPoints (image s S) X).ncard = 6

omit [Finite G] [Finite X] in
theorem base_subset_fixed (s : Set X) (S : Sylow 2 (fixingSubgroup G s)) :
    s ⊆ fixedPoints (image s S) X := by
  intro x hx
  rw [mem_fixedPoints]
  intro q
  obtain ⟨u,hu,he⟩ := q.property
  change (q : G) • x = x
  change (u : G) = (q : G) at he
  rw [← he]
  exact (mem_fixingSubgroup_iff G).mp u.property x hx

omit [Finite G] [Finite X] in
theorem fixing_insert_le (s : Set X) (x : X) :
    fixingSubgroup G (insert x s) ≤ fixingSubgroup G s := by
  intro g hg
  rw [mem_fixingSubgroup_iff] at hg ⊢
  intro y hy
  exact hg y (Set.mem_insert_of_mem _ hy)

theorem triple_sylow_fixed_six
    (heven : Even (Nat.card X)) (hfour : FourFixedSix G X)
    (s : Set X) (hs : s.ncard = 3) (S : Sylow 2 (fixingSubgroup G s)) :
    (fixedPoints (image s S) X).ncard = 6 := by
  classical
  let H := fixingSubgroup G s
  let Q := image s S
  have hbase := base_subset_fixed s S
  have hge : 3 ≤ (fixedPoints Q X).ncard := by
    simpa only [hs] using Set.ncard_le_ncard hbase
  have hp : IsPGroup 2 Q := S.isPGroup'.map H.subtype
  have hm := hp.card_modEq_card_fixedPoints X
  change Nat.card X % 2 = Nat.card (fixedPoints Q X) % 2 at hm
  rw [Nat.card_coe_set_eq] at hm
  have hmod := Nat.even_iff.mp heven
  have hge4 : 4 ≤ (fixedPoints Q X).ncard := by omega
  obtain ⟨x,hx,hxs⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (show s.ncard < (fixedPoints Q X).ncard by omega)
  let K := fixingSubgroup G (insert x s)
  have hK : K ≤ H := fixing_insert_le s x
  have hQK : Q ≤ K := by
    intro q hq
    rw [mem_fixingSubgroup_iff]
    intro y hy
    rcases hy with rfl | hy
    · exact mem_fixedPoints.mp hx ⟨q,hq⟩
    · exact mem_fixedPoints.mp (hbase hy) ⟨q,hq⟩
  obtain ⟨T,hT⟩ := SetwiseSylowNormalizer.exists_sylow_intermediate H K hK S hQK
  have hs4 : (insert x s).ncard = 4 := by rw [Set.ncard_insert_of_notMem hxs, hs]
  have h := hfour (insert x s) hs4 T
  change (fixedPoints ((T : Subgroup K).map K.subtype) X).ncard = 6 at h
  rwa [hT] at h

theorem exists_triple_sylow_fixing
    (heven : Even (Nat.card X)) (hfour : FourFixedSix G X)
    (s : Set X) (hs : s.ncard = 3) (x : X) (hx : x ∉ s) :
    ∃ S : Sylow 2 (fixingSubgroup G s), x ∈ fixedPoints S X := by
  classical
  let H := fixingSubgroup G s
  let K := fixingSubgroup G (insert x s)
  have hKH : K ≤ H := fixing_insert_le s x
  let P : Sylow 2 K := Classical.choice inferInstance
  let A : Subgroup G := (P : Subgroup K).map K.subtype
  have hAH : A ≤ H := by
    rintro g ⟨u,hu,rfl⟩
    exact hKH u.property
  let B : Subgroup H := A.subgroupOf H
  have hA : IsPGroup 2 A := P.isPGroup'.map K.subtype
  have hB : IsPGroup 2 B := hA.of_injective
    (Subgroup.subgroupOfEquivOfLe hAH).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hAH).injective
  obtain ⟨S,hBS⟩ := hB.exists_le_sylow
  let Q := (S : Subgroup H).map H.subtype
  have hAQ : A ≤ Q := by
    intro a ha
    exact ⟨⟨a,hAH ha⟩, hBS ha, rfl⟩
  have hsub : fixedPoints Q X ⊆ fixedPoints A X := by
    intro y hy
    rw [mem_fixedPoints]
    intro a
    exact mem_fixedPoints.mp hy ⟨a.val,hAQ a.property⟩
  have hA6 : (fixedPoints A X).ncard = 6 :=
    hfour (insert x s) (by rw [Set.ncard_insert_of_notMem hx,hs]) P
  have hQ6 : (fixedPoints Q X).ncard = 6 := triple_sylow_fixed_six heven hfour s hs S
  have heq : fixedPoints Q X = fixedPoints A X :=
    Set.eq_of_subset_of_ncard_le hsub (by omega)
  have hxA : x ∈ fixedPoints A X := base_subset_fixed (insert x s) P (Set.mem_insert x s)
  have hxQ : x ∈ fixedPoints Q X := heq ▸ hxA
  refine ⟨S, ?_⟩
  rw [← OyamaMinimalOrbitChoice.fixedPoints_map_subtype H (S : Subgroup H)]
  exact hxQ

end FiveTransitive.OyamaTripleSylow

end CFSG
