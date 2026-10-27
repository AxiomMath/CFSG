module

public import CFSG.Permutation.FiveTransitive.WholeFixerPairBlock
public import CFSG.Permutation.FiveTransitive.OyamaConditionFourTransitive

public section

namespace CFSG

namespace FiveTransitive.WholeFixerPairPartition

open MulAction WholeFixerClosureGeometry

theorem degree_eq_thirty_eight
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X)
    (hwhole:∀s:Set X,s.ncard=4 → Nat.card (closure G s)=6)
    (a:G) (ha2:a^2=1) (ha:a≠1) (ha6:Nat.card (fixedBy X a)=6) : Nat.card X=38 := by
  classical
  let F := fixedBy X a
  have hex:∃x:X,x∉F := by
    by_contra! h
    have he:F=Set.univ := Set.eq_univ_of_forall h
    change Nat.card F=6 at ha6
    rw [he,Nat.card_univ] at ha6
    have hn := hcond.1
    omega
  obtain ⟨x,hx⟩ := hex
  have hax:a • x≠x := hx
  let C:Set X := {x,a • x}
  have hC:C.ncard=2 := Set.ncard_pair hax.symm
  have hxC:x∈C := Set.mem_insert x _
  have hCF:Disjoint C F := InvolutionPairSets.pair_disjoint_fixed a ha2 x hax
  have hCinv:∀z:X,z∈C ↔ a • z∈C := InvolutionPairSets.pair_invariant a ha2 x
  let Y := ↥((F∪C)ᶜ : Set X)
  let P := {U:Set X // U⊆F ∧ U.ncard=2}
  have hP:Nat.card P=15 := by
    change Nat.card ({U:Set X|U⊆F ∧ U.ncard=2})=15
    rw [Nat.card_coe_set_eq,Set.ncard_powerset_ncard (Set.toFinite F),←Nat.card_coe_set_eq,ha6]
    decide
  have hblock (U:P) := WholeFixerPairBlock.extra_pair hcond hwhole a ha2 ha C hC hCF hCinv
    x hxC U.val U.property.1 U.property.2
  let S:Y→Set X := fun y => C∪{y.val,a • y.val}
  have hSy (y:Y):(S y).ncard=4 := by
    have hyy:a • y.val≠y.val := fun h => y.property (Or.inl h)
    have hdis:Disjoint C ({y.val,a • y.val}:Set X) := by
      apply Set.disjoint_right.mpr
      intro z hz hzC
      rcases Set.mem_insert_iff.mp hz with rfl|hz
      · exact y.property (Or.inr hzC)
      · have he:z=a • y.val := Set.mem_singleton_iff.mp hz
        rw [he] at hzC
        exact y.property (Or.inr ((hCinv y.val).mpr hzC))
    change (C∪{y.val,a • y.val}).ncard=4
    rw [Set.ncard_union_eq hdis,hC,Set.ncard_pair hyy.symm]
  have hSinv (y:Y):∀z:X,z∈S y ↔ a • z∈S y := by
    intro z
    exact or_congr (hCinv z) (InvolutionPairSets.pair_invariant a ha2 y.val z)
  have hSyfix (y:Y):(F∩closure G (S y)).ncard=2 :=
    fixed_intersection_card_two hcond (S y) (hSy y) (hwhole _ (hSy y)) a ha2 ha (hSinv y)
      ⟨x,Or.inl hxC,hax⟩
  let φ:Y→P := fun y => ⟨F∩closure G (S y),Set.inter_subset_left,hSyfix y⟩
  have h4 := OyamaConditionFourTransitive.four_transitive hcond
  have hfiber (U:P) (y:Y):φ y=U ↔ y.val∈closure G (U.val∪C) \ (U.val∪C) := by
    constructor
    · intro h
      have heU:F∩closure G (S y)=U.val := congrArg Subtype.val h
      have hsub:U.val∪C⊆closure G (S y) := by
        intro z hz
        rcases hz with hzU|hzC
        · have hI:z∈F∩closure G (S y) := heU.symm ▸ hzU
          exact hI.2
        · exact subset_closure _ (Or.inl hzC)
      have heq := closure_eq_of_subset_closure h4 (S y) (U.val∪C) (hSy y) (hblock U).1 hsub
      refine ⟨?_,?_⟩
      · rw [←heq]
        exact subset_closure _ (Or.inr (Set.mem_insert y.val _))
      · intro hz
        rcases hz with hzU|hzC
        · exact y.property (Or.inl (U.property.1 hzU))
        · exact y.property (Or.inr hzC)
    · intro hy
      have hUinv := InvolutionPairSets.fixed_subset_invariant a ha2 U.val U.property.1
      have hbaseInv (z:X):z∈U.val∪C ↔ a • z∈U.val∪C := or_congr (hUinv z) (hCinv z)
      have hDinv := closure_invariant (U.val∪C) a hbaseInv
      have hsub:S y⊆closure G (U.val∪C) := by
        intro z hz
        rcases hz with hzC|hz
        · exact subset_closure _ (Or.inr hzC)
        · rcases Set.mem_insert_iff.mp hz with rfl|hz
          · exact hy.1
          · have he:z=a • y.val := Set.mem_singleton_iff.mp hz
            rw [he]
            exact (hDinv y.val).mp hy.1
      have heq := closure_eq_of_subset_closure h4 (U.val∪C) (S y) (hblock U).1 (hSy y) hsub
      apply Subtype.ext
      change F∩closure G (S y)=U.val
      rw [←heq]
      exact (hblock U).2.1
  have hcardFiber (U:P):Nat.card {y:Y // φ y=U}=2 := by
    let E:{y:Y // φ y=U} ≃ ↥(closure G (U.val∪C) \ (U.val∪C)) := {
      toFun := fun y => ⟨y.val.val,(hfiber U y.val).mp y.property⟩
      invFun := fun z => ⟨⟨z.val,(hblock U).2.2.2 z.property⟩,
        (hfiber U ⟨z.val,(hblock U).2.2.2 z.property⟩).mpr z.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    rw [Nat.card_congr E,Nat.card_coe_set_eq]
    exact (hblock U).2.2.1
  let _ := Fintype.ofFinite P
  have hYcard:Nat.card Y=30 := by
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card Y = ∑U:P,Fintype.card {y:Y // φ y=U} := by
        rw [←Fintype.card_sigma]
        exact (Fintype.card_congr (Equiv.sigmaFiberEquiv φ)).symm
      _ = ∑_U:P,2 := by
        apply Finset.sum_congr rfl
        intro U _hU
        rw [←Nat.card_eq_fintype_card,hcardFiber]
      _ = 30 := by simp [←Nat.card_eq_fintype_card,hP]
  have hY:Nat.card Y=Nat.card X-8 := by
    change Nat.card ((F∪C)ᶜ : Set X)=Nat.card X-8
    rw [Nat.card_coe_set_eq,Set.ncard_compl,Set.ncard_union_eq hCF.symm,hC,
      ←Nat.card_coe_set_eq,ha6]
  omega

end FiveTransitive.WholeFixerPairPartition

end CFSG
