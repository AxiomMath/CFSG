module

public import CFSG.Permutation.FiveTransitive.WholeFixerClosureGeometry
public import CFSG.Permutation.FiveTransitive.InvolutionPairSets

public section

namespace CFSG

namespace FiveTransitive.WholeFixerPairBlock

open MulAction WholeFixerClosureGeometry

theorem extra_pair
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X)
    (hwhole:∀s:Set X,s.ncard=4 → Nat.card (closure G s)=6)
    (a:G) (ha2:a^2=1) (ha:a≠1)
    (C:Set X) (hC:C.ncard=2) (hCF:Disjoint C (fixedBy X a))
    (hCinv:∀z:X,z∈C ↔ a • z∈C) (x:X) (hx:x∈C)
    (U:Set X) (hU:U⊆fixedBy X a) (hUc:U.ncard=2) :
    (U∪C).ncard=4 ∧ fixedBy X a ∩ closure G (U∪C)=U ∧
      (closure G (U∪C) \ (U∪C)).ncard=2 ∧
      closure G (U∪C) \ (U∪C)⊆(fixedBy X a∪C)ᶜ := by
  classical
  have hdis:Disjoint U C := by
    apply Set.disjoint_left.mpr
    intro z hzU hzC
    exact Set.disjoint_left.mp hCF hzC (hU hzU)
  have hB:(U∪C).ncard=4 := by rw [Set.ncard_union_eq hdis,hUc,hC]
  have hUinv := InvolutionPairSets.fixed_subset_invariant a ha2 U hU
  have hinv (z:X):z∈U∪C ↔ a • z∈U∪C := or_congr (hUinv z) (hCinv z)
  have hxmove:a • x≠x := by
    intro h
    exact Set.disjoint_left.mp hCF hx h
  have hfix2:(fixedBy X a∩closure G (U∪C)).ncard=2 :=
    fixed_intersection_card_two hcond (U∪C) hB (hwhole _ hB) a ha2 ha hinv
      ⟨x,Or.inr hx,hxmove⟩
  have hUI:U⊆fixedBy X a∩closure G (U∪C) := by
    intro z hz
    exact ⟨hU hz,subset_closure _ (Or.inl hz)⟩
  have hI:fixedBy X a∩closure G (U∪C)=U :=
    (Set.eq_of_subset_of_ncard_le hUI (by rw [hfix2,hUc])).symm
  refine ⟨hB,hI,?_,?_⟩
  · rw [Set.ncard_sdiff (subset_closure _),←Nat.card_coe_set_eq,hwhole _ hB,hB]
  · intro z hz hbad
    rcases hbad with hfix|hzC
    · have hzU:z∈U := hI ▸ (show z∈fixedBy X a∩closure G (U∪C) from ⟨hfix,hz.1⟩)
      exact hz.2 (Or.inl hzU)
    · exact hz.2 (Or.inr hzC)

end FiveTransitive.WholeFixerPairBlock

end CFSG
