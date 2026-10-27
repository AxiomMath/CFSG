module

public import CFSG.Permutation.FiveTransitive.OyamaConditionPair
public import CFSG.Permutation.FiveTransitive.LocalSylowFixedMaximal
public import CFSG.Permutation.FiveTransitive.BaseSylowConjugacy

public section

namespace CFSG

namespace FiveTransitive.OyamaNormalizerPair

open MulAction LocalSylowFixedMaximal

private theorem pair_sylow_fixed
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (u v:X) (huv:u≠v)
    (S:Sylow 2 (fixingSubgroup G {u,v})) :
    fixedPoints ((S:Subgroup (fixingSubgroup G {u,v})).map
      (fixingSubgroup G {u,v}).subtype) X={u,v} := by
  classical
  let H := fixingSubgroup G ({u,v}:Set X)
  obtain ⟨Q,hQ,hQfix⟩ := OyamaConditionPair.exists_pair_fixed_subgroup hcond u v huv
  have hQH:Q≤H := by
    intro q hq
    rw [mem_fixingSubgroup_iff]
    intro x hx
    exact mem_fixedPoints.mp (hQfix.symm ▸ hx) ⟨q,hq⟩
  obtain ⟨V,hQV⟩ := exists_sylow_containing H Q hQ hQH
  have hbase (R:Sylow 2 H):({u,v}:Set X)⊆fixedPoints ((R:Subgroup H).map H.subtype) X := by
    intro x hx
    rw [mem_fixedPoints]
    intro r
    obtain ⟨t,ht,he⟩ := r.property
    change r.val • x=x
    rw [←he]
    exact (mem_fixingSubgroup_iff G).mp t.property x hx
  have hV:fixedPoints ((V:Subgroup H).map H.subtype) X={u,v} := by
    apply le_antisymm ?_ (hbase V)
    intro x hx
    rw [←hQfix]
    exact mem_fixedPoints.mpr fun q => mem_fixedPoints.mp hx ⟨q.val,hQV q.property⟩
  obtain ⟨c,hc⟩ := BaseSylowConjugacy.exists_conjugate_sylow_images G X 2
    (OyamaConditionPair.two_transitive hcond) {u,v} {u,v}
    (Set.ncard_pair huv) (Set.ncard_pair huv) V S
  have hcard:Nat.card (fixedPoints ((S:Subgroup H).map H.subtype) X)=2 := by
    rw [←hc]
    rw [←AmbientConjugateFixedSet.card_fixedPoints_conjugate ((V:Subgroup H).map H.subtype) c]
    rw [hV,Nat.card_coe_set_eq,Set.ncard_pair huv]
  apply (Set.eq_of_subset_of_ncard_le (hbase S) ?_).symm
  rw [←Nat.card_coe_set_eq,hcard,Set.ncard_pair huv]

theorem exists_pair_in_normalizer
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (b:Fin 4 ↪ X)
    (P:Sylow 2 (stabilizer G b)) (u v:X) (huv:u≠v)
    (hu:u∈fixedPoints ((P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype) X)
    (hv:v∈fixedPoints ((P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype) X) :
    let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
    ∃T:Subgroup G,IsPGroup 2 T ∧ T≤Subgroup.normalizer (A:Set G) ∧
      A<T ∧ fixedPoints T X={u,v} := by
  classical
  let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
  let H := fixingSubgroup G ({u,v}:Set X)
  have hAH:A≤H := by
    intro a ha
    rw [mem_fixingSubgroup_iff]
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl|hx
    · exact mem_fixedPoints.mp hu ⟨a,ha⟩
    · have he:x=v := Set.mem_singleton_iff.mp hx
      subst x
      exact mem_fixedPoints.mp hv ⟨a,ha⟩
  obtain ⟨S,hAS⟩ := exists_sylow_containing H A
    (P.isPGroup'.map (stabilizer G b).subtype) hAH
  let B := (S:Subgroup H).map H.subtype
  have hBfix:fixedPoints B X={u,v} := pair_sylow_fixed hcond u v huv S
  have hAfix:Nat.card (fixedPoints A X)=6 := (hcond.2.1 b P).1
  have hAB:A<B := by
    apply lt_of_le_of_ne hAS
    intro he
    rw [he,hBfix,Nat.card_coe_set_eq,Set.ncard_pair huv] at hAfix
    omega
  have hB:IsPGroup 2 B := S.isPGroup'.map H.subtype
  let T := B ⊓ Subgroup.normalizer (A:Set G)
  have hAT:A<T := lt_inf_normalizer B A hB hAB
  have hT:IsPGroup 2 T := hB.of_injective
    (Subgroup.inclusion (show T≤B from inf_le_left)) (Subgroup.inclusion_injective _)
  have hbase:({u,v}:Set X)⊆fixedPoints T X := by
    intro x hx
    have hxB:x∈fixedPoints B X := hBfix.symm ▸ hx
    exact mem_fixedPoints.mpr fun t => mem_fixedPoints.mp hxB ⟨t.val,t.property.1⟩
  have hlt:Nat.card (fixedPoints T X)<4 := by
    by_contra hn
    have he := eq_of_four_fixed hcond.2.1 b P T hT hAT.le (by omega)
    exact hAT.ne he.symm
  have hmod := hT.card_modEq_card_fixedPoints X
  have hdeg := EvenSixDegreeBound.degree_mod_two (by have := hcond.1; omega) hcond.2.1
  change Nat.card X % 2=Nat.card (fixedPoints T X) % 2 at hmod
  have hge:2≤Nat.card (fixedPoints T X) := by
    rw [Nat.card_coe_set_eq]
    simpa only [Set.ncard_pair huv] using Set.ncard_le_ncard hbase
  have hcard:Nat.card (fixedPoints T X)=2 := by omega
  refine ⟨T,hT,inf_le_right,hAT,?_⟩
  apply (Set.eq_of_subset_of_ncard_le hbase ?_).symm
  rw [←Nat.card_coe_set_eq,hcard,Set.ncard_pair huv]

end FiveTransitive.OyamaNormalizerPair

end CFSG
