module

public import CFSG.Permutation.FiveTransitive.OyamaConditionSylowTwo

public section

namespace CFSG

namespace FiveTransitive.OyamaTripleFixerOdd

open MulAction

theorem sylow_card_eq_two
    {G X:Type} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (s:Set X) (hs:s.ncard=3)
    (S:Sylow 2 (fixingSubgroup G s)) : Nat.card S=2 := by
  classical
  have hfour:OyamaTripleSylow.FourFixedSix G X := by
    intro t ht T
    exact (EvenSixTupleLocal.to_set_property hcond.2.1 t ht T).1
  have hfourcard (t:Set X) (ht:t.ncard=4) (T:Sylow 2 (fixingSubgroup G t)) : Nat.card T=2 := by
    obtain ⟨b,hb⟩ := BaseSylowConjugacy.exists_embedding_range X 4 t ht
    subst t
    revert T
    rw [EvenSixTupleLocal.fixing_range]
    exact OyamaConditionSylowTwo.card_eq_two hcond b
  have heven:Even (Nat.card X) := Nat.even_iff.mpr
    (EvenSixDegreeBound.degree_mod_two (by have := hcond.1; omega) hcond.2.1)
  let H := fixingSubgroup G s
  let Q := OyamaTripleSylow.image s S
  have hsix:(fixedPoints Q X).ncard=6 := OyamaTripleSylow.triple_sylow_fixed_six heven hfour s hs S
  obtain ⟨x,hx,hxs⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (show s.ncard<(fixedPoints Q X).ncard by omega)
  let K := fixingSubgroup G (insert x s)
  have hKH:K≤H := OyamaTripleSylow.fixing_insert_le s x
  have hQK:Q≤K := by
    intro q hq
    rw [mem_fixingSubgroup_iff]
    intro y hy
    rcases hy with rfl|hy
    · exact mem_fixedPoints.mp hx ⟨q,hq⟩
    · exact mem_fixedPoints.mp (OyamaTripleSylow.base_subset_fixed s S hy) ⟨q,hq⟩
  obtain ⟨T,hT⟩ := SetwiseSylowNormalizer.exists_sylow_intermediate H K hKH S hQK
  have hs4:(insert x s).ncard=4 := by rw [Set.ncard_insert_of_notMem hxs,hs]
  have hTcard:Nat.card T=2 := hfourcard (insert x s) hs4 T
  let eS:S ≃* Q := (S:Subgroup H).equivMapOfInjective H.subtype H.subtype_injective
  let eT:T ≃* ((T:Subgroup K).map K.subtype) :=
    (T:Subgroup K).equivMapOfInjective K.subtype K.subtype_injective
  calc
    Nat.card S = Nat.card Q := Nat.card_congr eS.toEquiv
    _ = Nat.card ((T:Subgroup K).map K.subtype) := congrArg (fun A:Subgroup G => Nat.card A) hT.symm
    _ = Nat.card T := (Nat.card_congr eT.toEquiv).symm
    _ = 2 := hTcard

end FiveTransitive.OyamaTripleFixerOdd

end CFSG
