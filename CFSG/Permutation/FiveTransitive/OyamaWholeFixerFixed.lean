module

public import CFSG.Permutation.FiveTransitive.WholeFixerPairPartition
public import CFSG.Permutation.FiveTransitive.OyamaWholeFixerCard

public section

namespace CFSG

namespace FiveTransitive.OyamaWholeFixerFixed

open MulAction WholeFixerClosureGeometry

private theorem not_fixed_six
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (s:Set X) (hs:s.ncard=4) :
    Nat.card (fixedPoints (fixingSubgroup G s) X)≠6 := by
  classical
  intro h6
  have h4 := OyamaConditionFourTransitive.four_transitive hcond
  have hwhole:∀t:Set X,t.ncard=4 → Nat.card (closure G t)=6 := by
    intro t ht
    exact (FourFixerClosure.card_data h4 s t hs ht).2.symm.trans h6
  obtain ⟨b,_hb⟩ := BaseSylowConjugacy.exists_embedding_range X 4 s hs
  let P:Sylow 2 (stabilizer G b) := Classical.arbitrary _
  let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
  obtain ⟨hne,hsq,_hcomm,_hsemi⟩ := hcond.2.2 b P
  have : Nontrivial A := A.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨a,ha⟩ := exists_ne (1:A)
  have haG:a.val≠1 := fun h => ha (Subtype.ext h)
  have ha2:a.val^2=1 := by
    simpa only [pow_two,Subgroup.coe_mul,Subgroup.coe_one] using congrArg Subtype.val (hsq a)
  have haFix:fixedBy X a.val=fixedPoints A X := OyamaCommutingPair.fixedBy_eq hcond b P a.val a.property haG
  have ha6:Nat.card (fixedBy X a.val)=6 := by
    rw [haFix]
    exact (hcond.2.1 b P).1
  have hdegree := WholeFixerPairPartition.degree_eq_thirty_eight hcond hwhole a.val ha2 haG ha6
  have hdiv := OyamaWholeFixerCard.three_divides_degree_of_fixed_six hcond s hs h6
  rw [hdegree] at hdiv
  norm_num at hdiv

theorem fixedPoints_eq
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (s:Set X) (hs:s.ncard=4) :
    fixedPoints (fixingSubgroup G s) X=s := by
  have hc:Nat.card (fixedPoints (fixingSubgroup G s) X)=4 := by
    rcases OyamaWholeFixerCard.fixed_card_four_or_six hcond s hs with h4|h6
    · exact h4
    · exact (not_fixed_six hcond s hs h6).elim
  apply (Set.eq_of_subset_of_ncard_le (subset_closure (G:=G) s) ?_).symm
  change (fixedPoints (fixingSubgroup G s) X).ncard≤s.ncard
  rw [←Nat.card_coe_set_eq,hc,hs]

end FiveTransitive.OyamaWholeFixerFixed

end CFSG
