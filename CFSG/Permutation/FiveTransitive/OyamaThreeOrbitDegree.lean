module

public import CFSG.Permutation.FiveTransitive.OyamaCommutingPair

public section

namespace CFSG

namespace FiveTransitive.OyamaThreeOrbitDegree

open MulAction CommutingInvolutionDegree

private theorem fixed_product
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (horb:OyamaThreeOrbitOrders.ThreeOrbits G X)
    (a b:G) (ha:a*a=1) (hb:b*b=1) (hab:a*b=b*a)
    (ha1:a≠1) (hb1:b≠1) (hne:a≠b) :
    fixedBy X (a*b)=(fixedBy X a ∩ fixedBy X b) ∪ (fixedBy X a ∪ fixedBy X b)ᶜ := by
  ext x
  constructor
  · intro hx
    by_cases hax:a • x=x
    · left
      refine ⟨hax,?_⟩
      apply MulAction.injective a
      exact (mul_smul a b x).symm.trans (hx.trans hax.symm)
    · right
      intro h
      rcases h with h|h
      · exact hax h
      · apply hax
        calc a • x = a • (b • x) := congrArg (fun y:X => a • y) h.symm
             _ = (a*b) • x := (mul_smul a b x).symm
             _ = x := hx
  · intro hx
    rcases hx with h|h
    · exact (mul_smul a b x).trans ((congrArg (fun y:X => a • y) h.2).trans h.1)
    · exact product_fixes_of_both_move hcond horb a b ha hb hab ha1 hb1 hne x
        (fun hax => h (Or.inl hax)) (fun hbx => h (Or.inr hbx))

theorem degree_ten_or_fourteen
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (horb:OyamaThreeOrbitOrders.ThreeOrbits G X) :
    Nat.card X=10 ∨ Nat.card X=14 := by
  classical
  obtain ⟨a,b,ha2,hb2,ha1,hb1,hne,hab,ha6,hb6,hi2⟩ := OyamaCommutingPair.exists_pair hcond horb
  have haa:a*a=1 := by simpa only [pow_two] using ha2
  have hbb:b*b=1 := by simpa only [pow_two] using hb2
  have hc2:(a*b)^2=1 := by
    rw [pow_two,←mul_assoc,hab,mul_assoc b a a,haa,mul_one,hbb]
  have hc1:a*b≠1 := by
    intro h
    have he := congrArg (fun g:G => g*b) h
    apply hne
    simpa only [mul_assoc,hbb,mul_one,one_mul] using he
  have he := fixed_product hcond horb a b haa hbb hab ha1 hb1 hne
  have hdis:Disjoint (fixedBy X a ∩ fixedBy X b) (fixedBy X a ∪ fixedBy X b)ᶜ := by
    apply Set.disjoint_left.mpr
    intro x hx hn
    exact hn (Or.inl hx.1)
  have hcfix:(fixedBy X (a*b)).ncard=2+(fixedBy X a ∪ fixedBy X b)ᶜ.ncard := by
    rw [he,Set.ncard_union_eq hdis,hi2]
  have hsum := Set.ncard_union_add_ncard_inter (fixedBy X a) (fixedBy X b)
  have htotal := Set.ncard_add_ncard_compl (fixedBy X a ∪ fixedBy X b)
  rw [Nat.card_coe_set_eq] at ha6 hb6
  have hU:(fixedBy X a ∪ fixedBy X b).ncard=10 := by omega
  have hC:Nat.card (fixedBy X (a*b))+8=Nat.card X := by
    rw [Nat.card_coe_set_eq]
    omega
  have hcge:2≤Nat.card (fixedBy X (a*b)) := by rw [Nat.card_coe_set_eq]; omega
  rcases fixed_two_or_six hcond (a*b) hc2 hc1 hcge with h|h <;> omega

end FiveTransitive.OyamaThreeOrbitDegree

end CFSG
