module

public import CFSG.Permutation.FiveTransitive.FourFixerClosure
public import CFSG.Permutation.FiveTransitive.NormalizerInvolutionFixedTwo
public import CFSG.Permutation.FiveTransitive.OyamaConditionStar
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

public section

namespace CFSG

namespace FiveTransitive.WholeFixerClosureGeometry

open MulAction

@[expose] def closure (G:Type*) {X:Type*} [Group G] [MulAction G X] (s:Set X) : Set X :=
  fixedPoints (fixingSubgroup G s) X

theorem subset_closure
    {G X:Type*} [Group G] [MulAction G X] (s:Set X) : s⊆closure G s := by
  intro x hx
  exact mem_fixedPoints.mpr fun a => (mem_fixingSubgroup_iff G).mp a.property x hx

private theorem fixer_eq_of_subset_closure
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h4:IsMultiplyPretransitive G X 4) (s t:Set X) (hs:s.ncard=4) (ht:t.ncard=4)
    (hst:t⊆closure G s) : fixingSubgroup G s=fixingSubgroup G t := by
  apply Subgroup.eq_of_le_of_card_ge
  · intro a ha
    rw [mem_fixingSubgroup_iff]
    intro x hx
    exact mem_fixedPoints.mp (hst hx) ⟨a,ha⟩
  · exact (FourFixerClosure.card_data h4 s t hs ht).1.symm.le

theorem closure_eq_of_subset_closure
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h4:IsMultiplyPretransitive G X 4) (s t:Set X) (hs:s.ncard=4) (ht:t.ncard=4)
    (hst:t⊆closure G s) : closure G s=closure G t := by
  unfold closure
  rw [fixer_eq_of_subset_closure h4 s t hs ht hst]

theorem closure_invariant
    {G X:Type*} [Group G] [MulAction G X] (s:Set X) (a:G)
    (ha:∀x:X,x∈s ↔ a • x∈s) : ∀x:X,x∈closure G s ↔ a • x∈closure G s := by
  have hn := SetwiseSylowNormalizer.normalizes_fixer s a ha
  intro x
  constructor
  · exact FixedSetNormalizerPerm.smul_mem_fixedPoints G X (fixingSubgroup G s) a hn
  · intro hx
    have h := FixedSetNormalizerPerm.smul_mem_fixedPoints G X (fixingSubgroup G s) a⁻¹
      ((Subgroup.normalizer (fixingSubgroup G s:Set G)).inv_mem hn) hx
    simpa only [closure,inv_smul_smul] using h

theorem fixed_intersection_card_two
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (s:Set X) (hs:s.ncard=4)
    (hC:Nat.card (closure G s)=6) (a:G) (ha2:a^2=1) (ha:a≠1)
    (hinv:∀x:X,x∈s ↔ a • x∈s) (hmove:∃x∈s,a • x≠x) :
    (fixedBy X a ∩ closure G s).ncard=2 := by
  classical
  let H := fixingSubgroup G s
  have hnorm:a∈Subgroup.normalizer (H:Set G) := SetwiseSylowNormalizer.normalizes_fixer s a hinv
  obtain ⟨P,hP⟩ := NormalizerInvariantSylow.exists_of_order_pow 2 G H a hnorm 1
    (by simpa only [pow_one] using orderOf_eq_prime ha2 ha)
  let A := (P:Subgroup H).map H.subtype
  have hsub:closure G s⊆fixedPoints A X := by
    intro x hx
    rw [mem_fixedPoints]
    intro q
    obtain ⟨h,hh,he⟩ := q.property
    change q.val • x=x
    rw [←he]
    exact mem_fixedPoints.mp hx h
  obtain ⟨hcard,heven⟩ := EvenSixTupleLocal.to_set_property hcond.2.1 s hs P
  have hEq:closure G s=fixedPoints A X := by
    apply Set.eq_of_subset_of_ncard_le hsub
    have hcardA:Nat.card (fixedPoints A X)=6 := by
      simpa only [Nat.card_coe_set_eq] using hcard
    rw [←Nat.card_coe_set_eq,←Nat.card_coe_set_eq,hcardA,hC]
  rw [hEq]
  apply NormalizerInvolutionFixedTwo.intersection_ncard_eq_two G X A a hP hcard ha2 (heven a hP)
  obtain ⟨x,hx,hax⟩ := hmove
  exact ⟨x,hsub (subset_closure s hx),hax⟩

end FiveTransitive.WholeFixerClosureGeometry

end CFSG
