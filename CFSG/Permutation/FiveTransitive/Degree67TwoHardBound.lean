module

public import CFSG.Permutation.FiveTransitive.Degree67TwoMixedKernel
public import CFSG.Permutation.FiveTransitive.Degree67QuadDerivedBound
public import CFSG.Permutation.FiveTransitive.TwoGroupSmallProjectionBound
public import CFSG.Permutation.FiveTransitive.TwoGroupQuadCommutatorProduct

public section

namespace CFSG

namespace FiveTransitive.Degree67TwoHardBound
open MulAction NormalizerOrbitFamily

theorem card_le
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Fintype X]
    (hcard : Fintype.card X = 67) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hF : Nat.card (fixedPoints Q X) = 5)
    (horbit : ∀ x : X, Nat.card (orbit Q x) ≤ 4)
    (hpair : 1 ≤ Nat.card (Family (X := X) Q 2))
    (hquad : 4 ≤ Nat.card (Family (X := X) Q 4))
    (hbound : ∀ q : Q, q ≠ 1 → Nat.card (fixedBy X q) ≤ 33) :
    Nat.card Q ≤ 65536 := by
  classical
  obtain ⟨A,B,rho,hA,hB,hRangeTwo,hRange,hKer,hFormula⟩ :=
    Degree67TwoMixedKernel.exists_projection hcard Q hQ hF horbit hbound hpair hquad
  obtain ⟨p⟩ : Nonempty (Family (X := X) Q 2) := Finite.card_pos_iff.mp hpair
  obtain ⟨x,hxmem⟩ := p.val.nonempty_orbit
  have he : (Quotient.mk'' x : orbitRel.Quotient Q X) = p.val :=
    orbitRel.Quotient.mem_orbit.mp hxmem
  have hx : Nat.card (orbit Q x) = 2 := by
    have hh := p.property
    rw [← he,orbitRel.Quotient.orbit_mk] at hh
    exact hh
  have hderived := Degree67QuadDerivedBound.commutator_card_le_eight
    hQ hcard hF horbit hbound x hx
  apply TwoGroupSmallProjectionBound.card_le hQ rho hKer hRange hderived
  intro hfull
  exact TwoGroupQuadCommutatorProduct.commutator_card_ge_sixteen
    hA hB rho.range hRangeTwo hfull

end FiveTransitive.Degree67TwoHardBound

end CFSG
