module

public import CFSG.Permutation.FiveTransitive.ThreeCycleColors
public import CFSG.Permutation.FiveTransitive.PGroupFixedOrbitInjective

public section

namespace CFSG

namespace FiveTransitive.FixedOrbitThreeRotation

open MulAction

theorem three_dvd_card
    {H Y:Type*} [Group H] [Finite H] [Finite Y] [MulAction H Y]
    (B:Subgroup H) (hB:IsPGroup 2 B)
    (hpoint:∀y:Y,∃T:Sylow 2 H,y∈fixedPoints T Y)
    (hfix:Nat.card (fixedPoints B Y)=3) (horb:Nat.card (orbitRel.Quotient H Y)=3)
    (r:Equiv.Perm Y) (q:Equiv.Perm (fixedPoints B Y))
    (hq3:q^3=1) (hqfree:∀z,q z≠z) (hq:∀z,(q z).val=r z.val)
    (hr:∀y z:Y,orbitRel H Y y z → orbitRel H Y (r y) (r z)) :
    3∣Nat.card Y := by
  classical
  let E:fixedPoints B Y ≃ orbitRel.Quotient H Y := Equiv.ofBijective
    (fun z => Quotient.mk'' z.val)
    ⟨PGroupFixedOrbitInjective.fixed_orbit_injective B hB hpoint (hfix.trans horb.symm),
     PGroupFixedOrbitInjective.fixed_orbit_surjective B hB hpoint⟩
  let c:Y→fixedPoints B Y := fun y => E.symm (Quotient.mk'' y)
  have hc:∀y,c (r y)=q (c y) := by
    intro y
    apply E.injective
    change E (E.symm (Quotient.mk'' (r y)))=Quotient.mk'' (q (c y)).val
    rw [E.apply_symm_apply,hq]
    apply Quotient.sound
    apply hr
    apply Quotient.exact
    exact (E.apply_symm_apply (Quotient.mk'' y)).symm
  exact ThreeCycleColors.three_dvd_card_of_equivariant hfix r q hq3 hqfree c hc

end FiveTransitive.FixedOrbitThreeRotation

end CFSG
