module

public import CFSG.Permutation.FiveTransitive.FourFixerClosure
public import CFSG.Permutation.FiveTransitive.OyamaConditionFourTransitive

public section

namespace CFSG

namespace FiveTransitive.OyamaWholeFixerCard

open MulAction

private theorem fixed_card_bounds
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (s:Set X) (hs:s.ncard=4) :
    4≤Nat.card (fixedPoints (fixingSubgroup G s) X) ∧
      Nat.card (fixedPoints (fixingSubgroup G s) X)≤6 := by
  classical
  let H := fixingSubgroup G s
  let P:Sylow 2 H := Classical.arbitrary _
  let A := (P:Subgroup H).map H.subtype
  have hbase:s⊆fixedPoints H X := by
    intro x hx
    exact mem_fixedPoints.mpr fun h => (mem_fixingSubgroup_iff G).mp h.property x hx
  have hsub:fixedPoints H X⊆fixedPoints A X := by
    intro x hx
    rw [mem_fixedPoints]
    intro a
    obtain ⟨h,hh,he⟩ := a.property
    change a.val • x=x
    rw [←he]
    exact mem_fixedPoints.mp hx h
  have h6:(fixedPoints A X).ncard=6 := (EvenSixTupleLocal.to_set_property hcond.2.1 s hs P).1
  have hlo := Set.ncard_le_ncard hbase
  have hhi := Set.ncard_le_ncard hsub
  rw [hs] at hlo
  rw [h6] at hhi
  exact ⟨by simpa only [Nat.card_coe_set_eq] using hlo,
    by simpa only [Nat.card_coe_set_eq] using hhi⟩

private theorem fixed_card_sub_three_dvd
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (s:Set X) (hs:s.ncard=4) :
    (Nat.card (fixedPoints (fixingSubgroup G s) X)-3)∣Nat.card X-3 := by
  classical
  let e:Fin 3 ↪ X := (Fin.castLEEmb (by have := hcond.1; omega : 3≤Nat.card X)).trans
    (Finite.equivFin X).symm.toEmbedding
  have he:(Set.range e).ncard=3 := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective e.injective
  have h4 := OyamaConditionFourTransitive.four_transitive hcond
  apply FourFixerClosure.fixed_card_sub_three_dvd h4 _ _ (Set.range e) he
  intro t ht
  exact (FourFixerClosure.card_data h4 s t hs ht).2.symm

theorem fixed_card_four_or_six
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (s:Set X) (hs:s.ncard=4) :
    Nat.card (fixedPoints (fixingSubgroup G s) X)=4 ∨
      Nat.card (fixedPoints (fixingSubgroup G s) X)=6 := by
  have hb := fixed_card_bounds hcond s hs
  have hnot:Nat.card (fixedPoints (fixingSubgroup G s) X)≠5 := by
    intro h5
    have hd := fixed_card_sub_three_dvd hcond s hs
    rw [h5] at hd
    have heven := EvenSixDegreeBound.degree_mod_two (by have := hcond.1; omega) hcond.2.1
    have hn := hcond.1
    obtain ⟨k,hk⟩ := hd
    omega
  omega

theorem three_divides_degree_of_fixed_six
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (s:Set X) (hs:s.ncard=4)
    (hfix:Nat.card (fixedPoints (fixingSubgroup G s) X)=6) : 3∣Nat.card X := by
  have hd := fixed_card_sub_three_dvd hcond s hs
  rw [hfix] at hd
  have hd':3∣(Nat.card X-3)+3 := dvd_add hd (dvd_refl 3)
  rwa [Nat.sub_add_cancel (by have := hcond.1; omega)] at hd'

end FiveTransitive.OyamaWholeFixerCard

end CFSG
