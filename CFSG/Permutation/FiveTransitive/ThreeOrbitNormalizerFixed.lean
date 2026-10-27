module

public import CFSG.Permutation.FiveTransitive.PGroupFixedOrbitInjective
public import CFSG.Permutation.FiveTransitive.OyamaTripleSylow
public import CFSG.Permutation.FiveTransitive.FixedSetNormalizerPerm

public section

namespace CFSG

namespace FiveTransitive.ThreeOrbitNormalizerFixed

open MulAction

theorem fixes_six_of_fixes_three
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (heven:Even (Nat.card X)) (hfour:OyamaTripleSylow.FourFixedSix G X)
    (s:Set X) (hs:s.ncard=3)
    (horbits:Nat.card (orbitRel.Quotient (fixingSubgroup G s)
      (SubMulAction.ofFixingSubgroup G s))=3)
    (A:Subgroup G) (hA:IsPGroup 2 A) (hAs:A≤fixingSubgroup G s)
    (hAfix:Nat.card (fixedPoints A X)=6)
    (g:G) (hgs:g∈fixingSubgroup G s) (hgA:g∈Subgroup.normalizer (A:Set G)) :
    ∀x∈fixedPoints A X,g • x=x := by
  classical
  let H := fixingSubgroup G s
  let Y := SubMulAction.ofFixingSubgroup G s
  let B := A.subgroupOf H
  have hB:IsPGroup 2 B := hA.of_injective
    (Subgroup.subgroupOfEquivOfLe hAs).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hAs).injective
  have hpoint (y:Y):∃T:Sylow 2 H,y∈fixedPoints T Y := by
    obtain ⟨T,hT⟩ := OyamaTripleSylow.exists_triple_sylow_fixing heven hfour s hs y.val y.property
    refine ⟨T,mem_fixedPoints.mpr fun t => ?_⟩
    exact Subtype.ext (mem_fixedPoints.mp hT t)
  have hbase:s⊆fixedPoints A X := by
    intro x hx
    exact mem_fixedPoints.mpr fun a => (mem_fixingSubgroup_iff G).mp (hAs a.property) x hx
  have hamb (y:fixedPoints B Y):y.val.val∈fixedPoints A X := by
    rw [mem_fixedPoints]
    intro a
    exact congrArg Subtype.val (mem_fixedPoints.mp y.property ⟨⟨a.val,hAs a.property⟩,a.property⟩)
  let E:fixedPoints B Y ≃ ↥(fixedPoints A X \ s) := {
    toFun := fun y => ⟨y.val.val,⟨hamb y,y.val.property⟩⟩
    invFun := fun x => ⟨⟨x.val,x.property.2⟩,mem_fixedPoints.mpr fun q =>
      Subtype.ext (mem_fixedPoints.mp x.property.1 ⟨q.val.val,q.property⟩)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hfixB:Nat.card (fixedPoints B Y)=3 := by
    rw [Nat.card_congr E,Nat.card_coe_set_eq,Set.ncard_sdiff hbase,←Nat.card_coe_set_eq,hAfix,hs]
  have hinj := PGroupFixedOrbitInjective.fixed_orbit_injective B hB hpoint
    (hfixB.trans horbits.symm)
  intro x hx
  by_cases hxs:x∈s
  · exact (mem_fixingSubgroup_iff G).mp hgs x hxs
  · let y:Y := ⟨x,hxs⟩
    have hy:y∈fixedPoints B Y := (E.symm ⟨x,⟨hx,hxs⟩⟩).property
    let k:H := ⟨g,hgs⟩
    have hky:k • y∈fixedPoints B Y := by
      rw [mem_fixedPoints]
      intro q
      apply Subtype.ext
      exact mem_fixedPoints.mp
        (FixedSetNormalizerPerm.smul_mem_fixedPoints G X A g hgA hx) ⟨q.val.val,q.property⟩
    have he: (⟨k • y,hky⟩:fixedPoints B Y)=⟨y,hy⟩ := by
      apply hinj
      apply Quotient.sound
      exact orbitRel_apply.mpr (mem_orbit y k)
    exact congrArg (fun z:fixedPoints B Y => z.val.val) he

end FiveTransitive.ThreeOrbitNormalizerFixed

end CFSG
