module

public import CFSG.Permutation.FiveTransitive.OyamaNormalizerPair
public import CFSG.Permutation.FiveTransitive.FixedSetNormalizerHom

public section

namespace CFSG

namespace FiveTransitive.OyamaNormalizerTwoTransitive

open MulAction

private theorem pair_in_image
    {G X:Type*} [Group G] [Finite G] [MulAction G X]
    (A T:Subgroup G) (hT:IsPGroup 2 T)
    (hTN:T≤Subgroup.normalizer (A:Set G))
    (u v:fixedPoints A X) (hfix:fixedPoints T X={u.val,v.val}) :
    ∃C:Subgroup (FixedSetNormalizerHom.fixedPermHom G X A).range,
      IsPGroup 2 C ∧ fixedPoints C (fixedPoints A X)={u,v} := by
  let N := Subgroup.normalizer (A:Set G)
  let f := FixedSetNormalizerHom.fixedPermHom G X A
  let B := T.subgroupOf N
  let C := B.map f.rangeRestrict
  have hB:IsPGroup 2 B := hT.of_injective
    (Subgroup.subgroupOfEquivOfLe hTN).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hTN).injective
  refine ⟨C,hB.map f.rangeRestrict,?_⟩
  have hmem (x:fixedPoints A X):x∈fixedPoints C (fixedPoints A X) ↔ x.val∈fixedPoints T X := by
    constructor
    · intro hx
      rw [mem_fixedPoints]
      intro t
      let n:N := ⟨t.val,hTN t.property⟩
      have hn:n∈B := t.property
      have ht := mem_fixedPoints.mp hx ⟨f.rangeRestrict n,⟨n,hn,rfl⟩⟩
      exact congrArg Subtype.val ht
    · intro hx
      rw [mem_fixedPoints]
      intro c
      obtain ⟨n,hn,he⟩ := c.property
      apply Subtype.ext
      change (c.val • x).val=x.val
      rw [←he]
      exact mem_fixedPoints.mp hx ⟨n.val,hn⟩
  ext x
  rw [hmem,hfix]
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro (h|h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl|rfl) <;> simp

theorem two_transitive
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (hcond:OyamaConditionStar.Condition G X) (b:Fin 4 ↪ X)
    (P:Sylow 2 (stabilizer G b)) :
    let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
    IsMultiplyPretransitive (FixedSetNormalizerHom.fixedPermHom G X A).range
      (fixedPoints A X) 2 := by
  let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
  apply OyamaPairCriterion.two_transitive_of_pair_fixed_sets
  · have hc := (hcond.2.1 b P).1
    change Nat.card (fixedPoints A X)=6 at hc
    change 3≤Nat.card (fixedPoints A X)
    omega
  · intro u v huv
    have huv':u.val≠v.val := fun h => huv (Subtype.ext h)
    obtain ⟨T,hT,hTN,_hAT,hfix⟩ := OyamaNormalizerPair.exists_pair_in_normalizer
      hcond b P u.val v.val huv' u.property v.property
    exact pair_in_image A T hT hTN u v hfix

theorem image_le_alternating
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hcond:OyamaConditionStar.Condition G X) (b:Fin 4 ↪ X)
    (P:Sylow 2 (stabilizer G b)) :
    let A := (P:Subgroup (stabilizer G b)).map (stabilizer G b).subtype
    letI := Fintype.ofFinite (fixedPoints A X)
    letI := Classical.decEq (fixedPoints A X)
    (FixedSetNormalizerHom.fixedPermHom G X A).range≤alternatingGroup (fixedPoints A X) := by
  intro A
  let _ := Fintype.ofFinite (fixedPoints A X)
  let _ : DecidableEq (fixedPoints A X) := Classical.decEq _
  intro f hf
  obtain ⟨n,rfl⟩ := hf
  apply Equiv.Perm.mem_alternatingGroup.mpr
  exact (hcond.2.1 b P).2 n.val n.property

end FiveTransitive.OyamaNormalizerTwoTransitive

end CFSG
