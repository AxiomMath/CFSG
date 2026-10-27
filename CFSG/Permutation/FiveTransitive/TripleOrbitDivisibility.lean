module

public import CFSG.Permutation.FiveTransitive.FixedOrbitThreeRotation
public import CFSG.Permutation.FiveTransitive.OyamaTripleSylow
public import CFSG.Permutation.FiveTransitive.FixedSetNormalizerPerm

public section

namespace CFSG

namespace FiveTransitive.TripleOrbitDivisibility

open MulAction

theorem three_dvd
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (heven:Even (Nat.card X)) (hfour:OyamaTripleSylow.FourFixedSix G X)
    (A:Subgroup G) (hA:IsPGroup 2 A) (hF:Nat.card (fixedPoints A X)=6)
    (g:G) (hg:g∈Subgroup.normalizer (A:Set G))
    (hσ3:(FixedSetNormalizerPerm.fixedPerm G X A g hg)^3=1)
    (hσfree:∀z:fixedPoints A X,FixedSetNormalizerPerm.fixedPerm G X A g hg z≠z)
    (s:Set X) (hs:s.ncard=3) (hbase:s⊆fixedPoints A X)
    (hpres:∀x:X,x∈s ↔ g • x∈s)
    (horb:Nat.card (orbitRel.Quotient (fixingSubgroup G s)
      (SubMulAction.ofFixingSubgroup G s))=3) : 3∣Nat.card X-3 := by
  classical
  let F := fixedPoints A X
  let H := fixingSubgroup G s
  let Y := SubMulAction.ofFixingSubgroup G s
  let B := A.subgroupOf H
  have hAs:A≤H := by
    intro a ha
    rw [mem_fixingSubgroup_iff]
    intro x hx
    exact mem_fixedPoints.mp (hbase hx) ⟨a,ha⟩
  have hB:IsPGroup 2 B := hA.of_injective
    (Subgroup.subgroupOfEquivOfLe hAs).toMonoidHom (Subgroup.subgroupOfEquivOfLe hAs).injective
  have hgn:g∈Subgroup.normalizer (H:Set G) := SetwiseSylowNormalizer.normalizes_fixer s g hpres
  let r:Equiv.Perm Y := (MulAction.toPerm g).subtypePerm (fun x => not_congr (hpres x).symm)
  have hrval (y:Y):(r y).val=g • y.val := rfl
  have hpoint (y:Y):∃T:Sylow 2 H,y∈fixedPoints T Y := by
    obtain ⟨T,hT⟩ := OyamaTripleSylow.exists_triple_sylow_fixing heven hfour s hs y.val y.property
    refine ⟨T,mem_fixedPoints.mpr fun t => ?_⟩
    exact Subtype.ext (mem_fixedPoints.mp hT t)
  have hamb (y:fixedPoints B Y):y.val.val∈F := by
    rw [mem_fixedPoints]
    intro a
    exact congrArg Subtype.val (mem_fixedPoints.mp y.property ⟨⟨a.val,hAs a.property⟩,a.property⟩)
  have hback (y:Y) (hy:y.val∈F):y∈fixedPoints B Y := by
    rw [mem_fixedPoints]
    intro a
    exact Subtype.ext (mem_fixedPoints.mp hy ⟨a.val.val,a.property⟩)
  let E:fixedPoints B Y ≃ ↥(F \ s) := {
    toFun := fun y => ⟨y.val.val,⟨hamb y,y.val.property⟩⟩
    invFun := fun x => ⟨⟨x.val,x.property.2⟩,hback ⟨x.val,x.property.2⟩ x.property.1⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hfixB:Nat.card (fixedPoints B Y)=3 := by
    rw [Nat.card_congr E,Nat.card_coe_set_eq,Set.ncard_sdiff hbase,←Nat.card_coe_set_eq,hF,hs]
  have hrfix (y:Y):r y∈fixedPoints B Y ↔ y∈fixedPoints B Y := by
    constructor
    · intro hy
      apply hback
      have hm := FixedSetNormalizerPerm.smul_mem_fixedPoints G X A g⁻¹
        ((Subgroup.normalizer (A:Set G)).inv_mem hg) (hamb ⟨r y,hy⟩)
      change g⁻¹ • (g • y.val)∈F at hm
      simpa only [inv_smul_smul] using hm
    · intro hy
      apply hback
      exact FixedSetNormalizerPerm.smul_mem_fixedPoints G X A g hg (hamb ⟨y,hy⟩)
  let q:Equiv.Perm (fixedPoints B Y) := r.subtypePerm hrfix
  have hqval (z:fixedPoints B Y):(q z).val=r z.val := rfl
  have hq3:q^3=1 := by
    apply Equiv.ext
    intro z
    apply Subtype.ext
    apply Subtype.ext
    have h := congrArg (fun u:Equiv.Perm F => (u ⟨z.val.val,hamb z⟩).val) hσ3
    change g • (g • (g • z.val.val))=z.val.val at h ⊢
    exact h
  have hqfree:∀z:fixedPoints B Y,q z≠z := by
    intro z hz
    apply hσfree ⟨z.val.val,hamb z⟩
    apply Subtype.ext
    exact congrArg (fun t:fixedPoints B Y => t.val.val) hz
  have hrOrbit:∀y z:Y,orbitRel H Y y z → orbitRel H Y (r y) (r z) := by
    intro y z hyz
    obtain ⟨a,ha⟩ := orbitRel_apply.mp hyz
    let k:H := ⟨g*a.val*g⁻¹,(Subgroup.mem_normalizer_iff.mp hgn a.val).mp a.property⟩
    apply orbitRel_apply.mpr
    refine ⟨k,?_⟩
    apply Subtype.ext
    have hav:a.val • z.val=y.val := congrArg Subtype.val ha
    change (g*a.val*g⁻¹) • (g • z.val)=g • y.val
    simp only [mul_smul,inv_smul_smul,hav]
  have hdiv := FixedOrbitThreeRotation.three_dvd_card B hB hpoint hfixB horb
    r q hq3 hqfree hqval hrOrbit
  have hY:Nat.card Y=Nat.card X-3 := by
    change Nat.card (sᶜ : Set X)=Nat.card X-3
    rw [Nat.card_coe_set_eq,Set.ncard_compl,hs]
  rwa [hY] at hdiv

end FiveTransitive.TripleOrbitDivisibility

end CFSG
